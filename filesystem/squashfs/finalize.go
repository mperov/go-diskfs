package squashfs

import (
	"encoding/binary"
	"fmt"
	"io"
	"os"
	"path"
	"path/filepath"
	"strings"
	"syscall"
	"time"

	"github.com/diskfs/go-diskfs/util"
	"github.com/pkg/xattr"
)

type fileType uint8

const (
	fileRegular fileType = iota
	fileDirectory
	fileSymlink
	fileBlock
	fileChar
	fileFifo
	fileSocket
)

// FinalizeOptions options to pass to finalize
type FinalizeOptions struct {
	// Compressor which compressor to use, including, where relevant, options. Defaults ot CompressorGzip
	Compression Compressor
	// NonExportable prevent making filesystem NFS exportable. Defaults to false, i.e. make it exportable
	NonExportable bool
	// NonSparse prevent detecting sparse files. Defaults to false, i.e. detect sparse files
	NonSparse bool
	// Xattrs whether or not to store extended attributes. Defaults to false
	Xattrs bool
	// NoCompressInodes whether or not to compress inodes. Defaults to false, i.e. compress inodes
	NoCompressInodes bool
	// NoCompressData whether or not to compress data blocks. Defaults to false, i.e. compress data
	NoCompressData bool
	// NoCompressFragments whether or not to compress fragments. Defaults to false, i.e. compress fragments
	NoCompressFragments bool
	// NoCompressXattrs whether or not to compress extended attrbutes. Defaults to false, i.e. compress xattrs
	NoCompressXattrs bool
	// NoFragments do not use fragments, but rather dedicated data blocks for all files. Defaults to false, i.e. use fragments
	NoFragments bool
	// NoPad do not pad filesystem so it is a multiple of 4K. Defaults to false, i.e. pad it
	NoPad bool
	// FileUID set all files to be owned by the UID provided, default is to leave as in filesystem
	FileUID *uint32
	// FileGID set all files to be owned by the GID provided, default is to leave as in filesystem
	FileGID *uint32
}

// Finalize finalize a read-only filesystem by writing it out to a read-only format
func (fs *FileSystem) Finalize(options FinalizeOptions) error {
	if fs.workspace == "" {
		return fmt.Errorf("Cannot finalize an already finalized filesystem")
	}

	/*
		There is nothing we can find about the order of files/directories, for any of:
		- inodes in inode table
		- entries in directory table
		- data in data section
		- fragments in fragment section

		to keep it simple, we will follow what mksquashfs on linux does, in the following order:
		- superblock at byte 0
		- compression options, if any, at byte 96
		- file data immediately following compression options (or superblock, if no compression options)
		- fragments immediately following file data
		- inode table
		- directory table
		- fragment table
		- export table
		- uid/gid lookup table
		- xattr table

		Note that until we actually copy and compress each section, we do not know the position of each subsequent
		section. So we have to write one, keep track of it, then the next, etc.


	*/

	f := fs.file
	blocksize := int(fs.blocksize)
	comp := compressionNone
	if options.Compression != nil {
		comp = options.Compression.flavour()
	}

	// build out file and directory tree
	// this returns a slice of *finalizeFileInfo, each of which represents a directory
	// or file
	fileList, err := walkTree(fs.Workspace())
	if err != nil {
		return fmt.Errorf("Error walking tree: %v", err)
	}

	// location holds where we are writing in our file
	var (
		location int64
		b        []byte
	)
	location += superblockSize
	if options.Compression != nil {
		b = options.Compression.optionsBytes()
		if len(b) > 0 {
			f.WriteAt(b, location)
			location += int64(len(b))
		}
	}

	// next write the file blocks
	compressor := options.Compression
	if options.NoCompressData {
		compressor = nil
	}

	// write file data blocks
	//
	dataWritten, err := writeDataBlocks(fileList, f, fs.workspace, blocksize, compressor, location)
	if err != nil {
		return fmt.Errorf("Error writing file data blocks: %v", err)
	}
	location += int64(dataWritten)

	//
	// write file fragments
	//
	fragmentBlockStart := location
	fragmentBlocks, fragsWritten, err := writeFragmentBlocks(fileList, f, fs.workspace, blocksize, options, fragmentBlockStart)
	if err != nil {
		return fmt.Errorf("Error writing file fragment blocks: %v", err)
	}
	location += int64(fragsWritten)

	// extract extended attributes, and save them for later; these are written at the very end
	// this must be done *before* creating inodes, as inodes reference these
	xattrs := extractXattrs(fileList)

	// Now we need to write the inode table and directory table. But
	// we have a chicken and an egg problem.
	//
	// * On the one hand, inodes are written to the disk before the directories, so we need to know
	// the size of the inode data.
	// * On the other hand, inodes for directories point to directories, specifically, the block and offset
	// where the pointed-at directory resides in the directory table.
	//
	// So we need inode table to create directory table, and directory table to create inode table.
	//
	// Further complicating matters is that the data in the
	// directory inodes relies on having the directory data ready. Specifically,
	// it includes:
	// - index of the block in the directory table where the dir info starts. Note
	//   that this is not just the directory *table* index, but the *block* index.
	// - offset within the block in the directory table where the dir info starts.
	//   Same notes as previous entry.
	// - size of the directory table entries for this directory, all of it. Thus,
	//   you have to have converted it all to bytes to get the information.
	//
	// The only possible way to do this is to run one, then the other, then
	// modify them. Until you generate both, you just don't know.
	//
	// Something that eases it a bit is that the block index in directory inodes
	// is from the start of the directory table, rather than start of archive.
	//
	// Order of execution:
	// 1. Write the file (not directory) data and fragments to disk.
	// 2. Create inodes for the files. We cannot write them yet because we need to
	//    add the directory entries before compression.
	// 3. Convert the directories to a directory table. And no, we cannot just
	//    calculate it based on the directory size, since some directories have
	//    one header, some have multiple, so the size of each directory, even
	//    given the number of files, can change.
	// 4. Create inodes for the directories and write them to disk
	// 5. Update the directory entries based on the inodes.
	// 6. Write directory table to disk
	//
	// if storing the inodes and directory table entirely in memory becomes
	// burdensome, use temporary scratch disk space to cache data in flight

	//
	// Build inodes for files. They are saved onto the fileList items themselves.
	//
	// build up a table of uids/gids we can store later
	idtable := map[uint32]uint16{}
	// get the inodes in order as a slice
	inodes, err := createInodes(fileList, idtable, options)
	if err != nil {
		return fmt.Errorf("error creating file inodes: %v", err)
	}

	// convert the inodes to data, while keeping track of where each
	// one is, so we can update the directory entries
	inodeLocations := getInodeLocations(inodes)

	// create the directory table. We already have every inode and its position,
	// so we do not need to dip back into the inodes. The only changes will be
	// the block/offset references into the directory table, but those sizes do
	// no change. However, we will have to break out the headers, so this is not
	// completely finalized yet.
	directories := createDirectories(fileList[0], inodeLocations)

	// create the final version of the directory table by creating the headers
	// and entries.
	dirTable := optimizeDirectoryTable(directories)

	directoryLocations := getDirectoryLocations(dirTable)

	if err := updateInodesFromDirectories(inodes, dirTable, directoryLocations); err != nil {
		return fmt.Errorf("error updating inodes with final directory data: %v", err)
	}

	// write the inodes to the file
	inodesWritten, inodeTableLocation, err := writeInodes(inodes, f, compressor, location)
	if err != nil {
		return fmt.Errorf("Error writing inode data blocks: %v", err)
	}
	location += int64(inodesWritten)

	// write directory data
	dirsWritten, dirTableLocation, err := writeDirectories(dirTable, directoryLocations, f, compressor, location)
	if err != nil {
		return fmt.Errorf("Error writing directory data blocks: %v", err)
	}
	location += int64(dirsWritten)

	// write fragment table

	/*
		The indexCount is used for indexed lookups.

		The index is stored at the end of the inode (after the filename) for extended directory
		There is one entry for each block after the 0th, so if there is just one block, then there is no index
		The filenames in the directory are sorted alphabetically. Each entry gives the first filename found in
		the respective block, so if the name found is larger than yours, it is in the previous block

		b[0:4] uint32 index - number of bytes where this entry is from the beginning of this directory
		b[4:8] uint32 startBlock - number of bytes in the filesystem from the start of the directory table that this block is
		b[8:12] uint32 size - size of the name (-1)
		b[12:12+size] string name

		Here is an example of 1 entry:

		f11f 0000 0000 0000 0b00 0000 6669 6c65 6e61 6d65 5f34 3638

		b[0:4] index 0x1ff1
		b[4:8] startBlock 0x00
		b[8:12] size 0x0b (+1 for a total of 0x0c = 12)
		b[12:24] name filename_468
	*/

	// TODO:
	/*
		 FILL IN:
		 - xattr table

		ALSO:
		- we have been treating every file like it is a normal file, but need to handle all of the special cases:
				- symlink, IPC, block/char device, hardlink
		- deduplicate values in xattrs
		- utilize options to: not add xattrs; not compress things; etc.
		- blockPosition calculations appear to be off

	*/

	// write the fragment table and its index
	fragmentTableWritten, fragmentTableLocation, err := writeFragmentTable(fragmentBlocks, fragmentBlockStart, f, compressor, location)
	if err != nil {
		return fmt.Errorf("Error writing fragment table: %v", err)
	}
	location += int64(fragmentTableWritten)

	// write the export table
	var (
		exportTableLocation uint64
		exportTableWritten  int
	)
	if !options.NonExportable {
		exportTableWritten, exportTableLocation, err = writeExportTable(inodeLocations, f, compressor, location)
		if err != nil {
			return fmt.Errorf("Error writing export table: %v", err)
		}
		location += int64(exportTableWritten)
	}

	// write the uidgid table
	idTableWritten, idTableLocation, err := writeIdTable(idtable, f, compressor, location)
	if err != nil {
		return fmt.Errorf("Error writing uidgid table: %v", err)
	}
	location += int64(idTableWritten)

	// write the xattrs
	xAttrsWritten, xAttrsLocation, err := writeXattrs(xattrs, f, compressor, location)
	if err != nil {
		return fmt.Errorf("Error writing xattrs table: %v", err)
	}
	location += int64(xAttrsWritten)

	// update and write the superblock
	sb := &superblock{
		blocksize:           uint32(blocksize),
		compression:         comp,
		inodes:              uint32(len(inodes)),
		xattrTableStart:     xAttrsLocation,
		fragmentCount:       uint32(len(fragmentBlocks)),
		modTime:             time.Now(),
		size:                uint64(location),
		versionMajor:        4,
		versionMinor:        0,
		idTableStart:        idTableLocation,
		exportTableStart:    exportTableLocation,
		inodeTableStart:     inodeTableLocation,
		idCount:             uint16(len(idtable)),
		directoryTableStart: dirTableLocation,
		fragmentTableStart:  fragmentTableLocation,
		rootInode:           &inodeRef{0, 0},
		superblockFlags: superblockFlags{
			uncompressedInodes:    options.NoCompressInodes,
			uncompressedData:      options.NoCompressData,
			uncompressedFragments: options.NoCompressFragments,
			uncompressedXattrs:    options.NoCompressXattrs,
			noFragments:           options.NoFragments,
			noXattrs:              !options.Xattrs,
			exportable:            !options.NonExportable,
		},
	}

	// write the superblock
	sbBytes := sb.toBytes()
	if _, err := f.WriteAt(sbBytes, 0); err != nil {
		return fmt.Errorf("failed to write superblock: %v", err)
	}

	// finish by setting as finalized
	fs.workspace = ""
	return nil
}

func copyFileData(from, to util.File, fromOffset, toOffset, blocksize int64, c Compressor) (int, int, []*blockData, error) {
	buf := make([]byte, blocksize)
	raw, compressed := 0, 0
	blocks := make([]*blockData, 0)
	for {
		n, err := from.ReadAt(buf, fromOffset+int64(raw))
		if err != nil && err != io.EOF {
			return raw, compressed, nil, err
		}
		if n != len(buf) {
			break
		}
		raw += len(buf)

		// compress the block if needed
		isCompressed := false
		if c != nil {
			out, err := c.compress(buf)
			if err != nil {
				return 0, 0, nil, fmt.Errorf("Error compressing block: %v", err)
			}
			if len(out) < len(buf) {
				isCompressed = true
				buf = out
			}
		}
		blocks = append(blocks, &blockData{size: uint32(len(buf)), compressed: isCompressed})
		if _, err := to.WriteAt(buf[:n], toOffset+int64(compressed)); err != nil {
			return raw, compressed, blocks, err
		}
		compressed += len(buf)
	}
	return raw, compressed, blocks, nil
}

// finalizeFragment write fragment data out to the archive, compressing if relevant.
// Returns the total amount written, whether compressed, and any error.
func finalizeFragment(buf []byte, to util.File, toOffset int64, c Compressor) (int, bool, error) {
	var compressed bool
	// compress the block if needed
	if c != nil {
		out, err := c.compress(buf)
		if err != nil {
			return 0, compressed, fmt.Errorf("Error compressing fragment block: %v", err)
		}
		if len(out) < len(buf) {
			buf = out
			compressed = true
		}
	}
	if _, err := to.WriteAt(buf, toOffset); err != nil {
		return 0, compressed, err
	}
	return len(buf), compressed, nil
}

// walkTree walks the tree and returns a slice of files and directories.
// We do files and directories differently, since they need to be processed
// differently on disk (file data and fragments vs directory table), and
// because the inode data is different.
// The first entry in the return always will be the root
func walkTree(workspace string) ([]*finalizeFileInfo, error) {
	cwd, err := os.Getwd()
	if err != nil {
		return nil, fmt.Errorf("Could not get pwd: %v", err)
	}
	// make everything relative to the workspace
	os.Chdir(workspace)
	dirMap := make(map[string]*finalizeFileInfo)
	fileList := make([]*finalizeFileInfo, 0)
	var entry *finalizeFileInfo
	filepath.Walk(".", func(fp string, fi os.FileInfo, err error) error {
		isRoot := fp == "."
		name := fi.Name()
		m := fi.Mode()
		var fType fileType
		switch {
		case m&os.ModeSocket == os.ModeSocket:
			fType = fileSocket
		case m&os.ModeSymlink == os.ModeSymlink:
			fType = fileSymlink
		case m&os.ModeNamedPipe == os.ModeNamedPipe:
			fType = fileFifo
		case m&os.ModeDir == os.ModeDir:
			fType = fileDirectory
		case m&os.ModeDevice == os.ModeDevice && m&os.ModeCharDevice == os.ModeCharDevice:
			fType = fileChar
		case m&os.ModeDevice == os.ModeDevice && m&os.ModeCharDevice != os.ModeCharDevice:
			fType = fileBlock
		default:
			fType = fileRegular
		}
		xattrNames, err := xattr.List(fp)
		if err != nil {
			return fmt.Errorf("Unable to list xattrs for %s: %v", fp, err)
		}
		xattrs := map[string]string{}
		for _, name := range xattrNames {
			val, err := xattr.Get(fp, name)
			if err != nil {
				return fmt.Errorf("Unable to get xattr %s for %s: %v", name, fp, err)
			}
			xattrs[name] = string(val)
		}
		var (
			nlink uint32
			uid   uint32
			gid   uint32
		)
		if sys := fi.Sys(); sys != nil {
			if stat, ok := sys.(*syscall.Stat_t); ok {
				nlink = uint32(stat.Nlink)
				uid = stat.Uid
				gid = stat.Gid
			}
		}

		entry = &finalizeFileInfo{
			path:     fp,
			name:     name,
			isDir:    fi.IsDir(),
			isRoot:   isRoot,
			modTime:  fi.ModTime(),
			mode:     m,
			fileType: fType,
			size:     fi.Size(),
			xattrs:   xattrs,
			uid:      uid,
			gid:      gid,
			links:    nlink,
		}

		// we will have to save it as its parent
		parentDir := filepath.Dir(fp)
		parentDirInfo := dirMap[parentDir]

		if fi.IsDir() {
			entry.children = make([]*finalizeFileInfo, 0, 20)
			dirMap[fp] = entry
		} else {
			// calculate blocks
			entry.size = fi.Size()
		}
		if !isRoot {
			parentDirInfo.children = append(parentDirInfo.children, entry)
			dirMap[parentDir] = parentDirInfo
		}
		fileList = append(fileList, entry)
		return nil
	})
	// reset the workspace
	os.Chdir(cwd)

	return fileList, nil
}

func getTableIdx(m map[uint32]uint16, index uint32) uint16 {
	for k, v := range m {
		if k == index {
			return v
		}
	}
	// if we made it this far it doesn't exist, so add it
	m[index] = uint16(len(m))
	return m[index]
}

func getDeviceNumbers(path string) (uint32, uint32, error) {
	stat := syscall.Stat_t{}
	err := syscall.Stat("/dev/sda", &stat)
	if err != nil {
		return 0, 0, err
	}
	return uint32(stat.Rdev / 256), uint32(stat.Rdev % 256), nil
}

func writeFileDataBlocks(e *finalizeFileInfo, to util.File, ws string, startBlock uint64, blocksize int, compressor Compressor, location int64) (int, int, error) {
	from, err := os.Open(path.Join(ws, e.path))
	if err != nil {
		return 0, 0, fmt.Errorf("failed to open file for reading %s: %v", e.path, err)
	}
	defer from.Close()
	raw, compressed, blocks, err := copyFileData(from, to, 0, location, int64(blocksize), compressor)
	if err != nil {
		return 0, 0, fmt.Errorf("Error copying file %s: %v", e.Name(), err)
	}
	if raw%blocksize != 0 {
		return 0, 0, fmt.Errorf("Copying file %s copied %d which is not a multiple of blocksize %d", e.Name(), raw, blocksize)
	}
	// save the information we need for usage later in inodes to find the file data
	e.dataLocation = location
	e.blocks = blocks
	e.startBlock = startBlock

	// how many blocks did we write?
	blockCount := raw / blocksize

	return blockCount, compressed, nil
}

func writeMetadataBlock(buf []byte, to util.File, c Compressor, location int64) (int, error) {
	// compress the block if needed
	isCompressed := false
	if c != nil {
		out, err := c.compress(buf)
		if err != nil {
			return 0, fmt.Errorf("Error compressing block: %v", err)
		}
		if len(out) < len(buf) {
			isCompressed = true
			buf = out
		}
	}
	// the 2-byte (16-bit) header gives the block size
	// the top bit is set if uncompressed
	size := uint16(len(buf))
	if !isCompressed {
		size = size | 1<<15
	}
	header := make([]byte, 2)
	binary.LittleEndian.PutUint16(header, size)
	buf = append(header, buf...)
	if _, err := to.WriteAt(buf, location); err != nil {
		return 0, err
	}
	return len(buf), nil
}

func writeDataBlocks(fileList []*finalizeFileInfo, f util.File, ws string, blocksize int, compressor Compressor, location int64) (int, error) {
	allBlocks := 0
	allWritten := 0
	for _, e := range fileList {
		// only copy data for normal files
		if e.fileType != fileRegular {
			continue
		}

		blocks, written, err := writeFileDataBlocks(e, f, ws, uint64(allBlocks), blocksize, compressor, location)
		if err != nil {
			return allWritten, fmt.Errorf("Error writing data for %s to file: %v", e.path, err)
		}
		allBlocks += blocks
		allWritten += written
	}
	return allWritten, nil
}

// writeFragmentBlocks writes all of the fragment blocks to the archive. Returns slice of blocks written, the total bytes written, any error
func writeFragmentBlocks(fileList []*finalizeFileInfo, f util.File, ws string, blocksize int, options FinalizeOptions, location int64) ([]fragmentBlock, int64, error) {
	compressor := options.Compression
	if options.NoCompressFragments {
		compressor = nil
	}
	fragmentData := make([]byte, 0)
	var (
		allWritten         int64
		fragmentBlockIndex uint32
		fragmentBlocks     []fragmentBlock
	)
	for _, e := range fileList {
		// only copy data for regular files
		if e.fileType != fileRegular {
			continue
		}
		var (
			written int64
			err     error
		)

		// how much is there to put in a fragment?
		remainder := e.Size() % int64(blocksize)
		if remainder == 0 {
			continue
		}

		// would adding this data cause us to write?
		if len(fragmentData)+int(remainder) > blocksize {
			written, compressed, err := finalizeFragment(fragmentData, f, location, compressor)
			if err != nil {
				return fragmentBlocks, 0, fmt.Errorf("error writing fragment block %d: %v", fragmentBlockIndex, err)
			}
			fragmentBlocks = append(fragmentBlocks, fragmentBlock{
				size:       uint32(written),
				compressed: compressed,
				location:   location,
			})
			// increment as all writes will be to next block block
			fragmentBlockIndex++
			fragmentData = fragmentData[:blocksize]
		}

		e.fragment = &fragmentRef{
			block:  fragmentBlockIndex,
			offset: uint32(len(fragmentData)),
		}
		// save the fragment data from the file

		from, err := os.Open(path.Join(ws, e.path))
		if err != nil {
			return fragmentBlocks, 0, fmt.Errorf("failed to open file for reading %s: %v", e.path, err)
		}
		defer from.Close()
		buf := make([]byte, remainder)
		n, err := from.ReadAt(buf, e.Size()-remainder)
		if err != nil && err != io.EOF {
			return fragmentBlocks, 0, fmt.Errorf("Error reading final %d bytes from file %s: %v", remainder, e.Name(), err)
		}
		if n != len(buf) {
			return fragmentBlocks, 0, fmt.Errorf("Failed reading final %d bytes from file %s, only read %d", remainder, e.Name(), n)
		}
		from.Close()
		fragmentData = append(fragmentData, buf...)

		allWritten += written
		if written > 0 {
			fragmentBlockIndex++
		}
	}

	// write remaining fragment data
	if len(fragmentData) > 0 {
		written, compressed, err := finalizeFragment(fragmentData, f, location, compressor)
		if err != nil {
			return fragmentBlocks, 0, fmt.Errorf("error writing fragment block %d: %v", fragmentBlockIndex, err)
		}
		fragmentBlocks = append(fragmentBlocks, fragmentBlock{
			size:       uint32(written),
			compressed: compressed,
		})
		// increment as all writes will be to next block block
		allWritten += int64(written)
	}
	return fragmentBlocks, allWritten, nil
}

func writeInodes(inodes []inode, f util.File, compressor Compressor, location int64) (int, uint64, error) {
	allWritten := 0
	var (
		buf             []byte
		maxSize         = int(metadataBlockSize)
		initialLocation = location
	)
	for _, i := range inodes {
		// keep writing until we run out, of we hit 8KB
		buf = append(buf, i.toBytes()...)
		if len(buf) > maxSize {
			written, err := writeMetadataBlock(buf[:maxSize], f, compressor, location)
			if err != nil {
				return allWritten, 0, err
			}
			// count all we have written
			allWritten += written
			// increment for next write
			location += int64(written)
			// truncate all except what we wrote
			buf = buf[maxSize:]
		}
	}
	// was there anything left?
	if len(buf) > 0 {
		written, err := writeMetadataBlock(buf, f, compressor, location)
		if err != nil {
			return allWritten, 0, err
		}
		allWritten += written
	}
	return allWritten, uint64(initialLocation), nil
}

// writeDirectories write all directories out to disk. Assumes it already has been optimized.
func writeDirectories(dirs []*directory, dirLocations []blockPosition, f util.File, compressor Compressor, location int64) (int, uint64, error) {
	allWritten := 0
	var (
		buf             []byte
		maxSize         = int(metadataBlockSize)
		initialLocation = location
	)
	for i, d := range dirs {
		// keep writing until we run out, of we hit 8KB
		dirLocation := dirLocations[i]
		buf = append(buf, d.toBytes(dirLocation.block, d.inodeIndex)...)
		if len(buf) > maxSize {
			written, err := writeMetadataBlock(buf[:maxSize], f, compressor, location)
			if err != nil {
				return allWritten, 0, err
			}
			// count all we have written
			allWritten += written
			// increment for next write
			location += int64(written)
			// truncate all except what we wrote
			buf = buf[maxSize:]
		}
	}
	// was there anything left?
	if len(buf) > 0 {
		written, err := writeMetadataBlock(buf, f, compressor, location)
		if err != nil {
			return allWritten, 0, err
		}
		allWritten += written
	}
	return allWritten, uint64(initialLocation), nil
}

// writeFragmentTable write the fragment table
func writeFragmentTable(fragmentBlocks []fragmentBlock, fragmentBlocksStart int64, f util.File, compressor Compressor, location int64) (int, uint64, error) {
	// before we can write the metadata blocks, we need to allocate space for the lookup table at the beginning
	initialLocation := location
	// each fragment block gets an entry, every 512 entries is another block with a lookup table pointer
	fragmentBlockCount := len(fragmentBlocks)
	indexEntryCount := fragmentBlockCount / 512
	if fragmentBlockCount%512 > 0 {
		indexEntryCount++
	}
	var indexEntries []uint64
	// jump forward enough space to write the table metadata blocks
	// each entry in the index table is uint64, or 8 bytes
	location += int64(indexEntryCount) * 8

	// now write the actual fragment table entries
	allWritten := 0
	var (
		buf     []byte
		maxSize = int(metadataBlockSize)
	)
	for _, block := range fragmentBlocks {
		// add an entry
		b := make([]byte, 16)
		size := block.size
		if block.compressed {
			size = size | 1<<24
		}
		binary.LittleEndian.PutUint64(b[0:8], uint64(block.location))
		binary.LittleEndian.PutUint32(b[8:12], size)

		buf = append(buf, b...)
		if len(buf) >= maxSize {
			written, err := writeMetadataBlock(buf[:maxSize], f, compressor, location)
			if err != nil {
				return allWritten, 0, err
			}
			// save an entry in the index table
			indexEntries = append(indexEntries, uint64(location))
			// count all we have written
			allWritten += written
			// increment for next write
			location += int64(written)
			// truncate all except what we wrote
			buf = buf[maxSize:]
		}
	}
	if len(buf) > 0 {
		written, err := writeMetadataBlock(buf, f, compressor, location)
		if err != nil {
			return allWritten, 0, err
		}
		// count all we have written
		allWritten += written
	}
	// now write the lookup table - 8 bytes for each entry
	buf = make([]byte, len(indexEntries)*8)
	for i, e := range indexEntries {
		binary.LittleEndian.PutUint64(buf[i*8:i*8+8], e)
	}
	// just write it out
	written, err := f.WriteAt(buf, initialLocation)
	if err != nil {
		return allWritten, 0, fmt.Errorf("error writing fragment table lookup index: %v", err)
	}
	allWritten += written
	return allWritten, uint64(initialLocation), nil
}

// writeExportTable write the export table at the given location.
func writeExportTable(inodes []blockPosition, f util.File, compressor Compressor, location int64) (int, uint64, error) {
	var (
		maxSize    = int(metadataBlockSize)
		allWritten int
	)

	// need to account for the index
	initialLocation := location
	// each inode gets an entry, every 1024 entries is another block with a lookup table pointer
	blockCount := len(inodes) * 8 / maxSize
	if blockCount > 0 {
		blockCount++
	}
	// jump forward and write the metadata blocks
	var indexEntries []uint64
	// jump forward and write the data
	location += int64(blockCount) * 8

	// the lookup table is pretty simple. It is just a single array of uint64. So inode 1 is in the first
	// entry, inode 2 in the second, etc. (inode 0 is reserved and unused).
	// The value of each entry is just the inode reference in the archive.
	// An "inode reference" is a 64-bit number structured as follows:
	// - upper 16 bits unused
	// - next 32 bits position of first byte of inode metadata block that contains this inode, relative to the start of the inode table
	// - lowest 16 bits are offset into the uncompressed block
	var buf []byte
	for _, in := range inodes {
		entry := make([]byte, 8)
		binary.LittleEndian.PutUint32(entry[2:6], in.block)
		binary.LittleEndian.PutUint16(entry[6:8], in.offset)
		buf = append(buf, entry...)
		if len(buf) >= maxSize {
			written, err := writeMetadataBlock(buf[:maxSize], f, compressor, location)
			if err != nil {
				return allWritten, 0, err
			}
			// count all we have written
			allWritten += written
			buf = buf[maxSize:]
			indexEntries = append(indexEntries, uint64(location))
			location += int64(written)
		}
	}
	// any leftover?
	if len(buf) > 0 {
		written, err := writeMetadataBlock(buf, f, compressor, location)
		if err != nil {
			return allWritten, 0, err
		}
		// count all we have written
		allWritten += written
		indexEntries = append(indexEntries, 0, uint64(location))
	}

	// now write the lookup table - 8 bytes for each entry
	buf = make([]byte, len(indexEntries)*8)
	for i, e := range indexEntries {
		binary.LittleEndian.PutUint64(buf[i*8:i*8+8], e)
	}
	// just write it out
	written, err := f.WriteAt(buf, initialLocation)
	if err != nil {
		return allWritten, 0, fmt.Errorf("error writing export table lookup index: %v", err)
	}
	allWritten += written
	return allWritten, uint64(initialLocation), nil
}

// writeIdTable write the uidgid table at the given location.
func writeIdTable(idtable map[uint32]uint16, f util.File, compressor Compressor, location int64) (int, uint64, error) {
	var (
		maxSize    = int(metadataBlockSize)
		allWritten int
	)

	// to write the idtable, we need to convert the map of target ID (uid/gid) -> index into an array by index
	idArray := make([]uint32, len(idtable))
	for k, v := range idtable {
		idArray[v] = k
	}

	// need to account for the index
	initialLocation := location
	// each element in idArray gets an entry, every 2048 entries is another block with a lookup table pointer
	blockCount := len(idArray) * 4 / maxSize
	if blockCount > 0 {
		blockCount++
	}
	// jump forward and write the metadata blocks
	var indexEntries []uint64
	// jump forward and write the data
	location += int64(blockCount) * 8

	// the lookup table is pretty simple. It is just a single array of uint32.
	// The value of each entry is just the ID number.
	var buf []byte
	for _, id := range idArray {
		entry := make([]byte, 4)
		binary.LittleEndian.PutUint32(entry, id)
		buf = append(buf, entry...)
		if len(buf) >= maxSize {
			written, err := writeMetadataBlock(buf[:maxSize], f, compressor, location)
			if err != nil {
				return allWritten, 0, err
			}
			// count all we have written
			allWritten += written
			buf = buf[maxSize:]
			indexEntries = append(indexEntries, uint64(location))
			location += int64(written)
		}
	}
	// any leftover?
	if len(buf) > 0 {
		written, err := writeMetadataBlock(buf, f, compressor, location)
		if err != nil {
			return allWritten, 0, err
		}
		// count all we have written
		allWritten += written
		indexEntries = append(indexEntries, uint64(location))
	}

	// now write the lookup table - 8 bytes for each entry
	buf = make([]byte, len(indexEntries)*8)
	for i, e := range indexEntries {
		binary.LittleEndian.PutUint64(buf[i*8:i*8+8], e)
	}
	// just write it out
	written, err := f.WriteAt(buf, initialLocation)
	if err != nil {
		return allWritten, 0, fmt.Errorf("error writing uidgid table lookup index: %v", err)
	}
	allWritten += written
	return allWritten, uint64(initialLocation), nil
}

// writeXattrs write the xattrs and its lookup table at the given location.
func writeXattrs(xattrs []map[string]string, f util.File, compressor Compressor, location int64) (int, uint64, error) {
	var (
		maxSize         = int(metadataBlockSize)
		allWritten      int
		offset          int
		lookupTable     []byte
		buf             []byte
		initialLocation = location
	)

	// each entry in the xattrs slice is a unique key-value map. It may be referenced by one or more inodes.
	// first convert them to key-value written pairs, and save where they are
	for _, m := range xattrs {
		// process one xattr key-value map
		var single []byte
		for k, v := range m {
			// convert it to the proper type
			// the entry
			prefix, name, err := xAttrKeyConvert(k)
			if err != nil {
				return allWritten, 0, err
			}
			b := make([]byte, 4)
			binary.LittleEndian.PutUint16(b[0:2], prefix)
			binary.LittleEndian.PutUint16(b[2:4], uint16(len(k)))
			b = append(b, []byte(name)...)
			single = append(single, b...)

			b = make([]byte, 4)
			binary.LittleEndian.PutUint32(b[0:4], uint32(len(v)))
			b = append(b, []byte(v)...)
			single = append(single, b...)
		}
		// add the index
		b := make([]byte, 16)
		// bits 16:48 (uint32) hold the block position
		binary.LittleEndian.PutUint32(b[2:6], uint32(allWritten))
		// bits 48:64 (uint16) hold the offset in the uncompressed block
		binary.LittleEndian.PutUint16(b[6:8], uint16(offset))
		// bytes 8:12 (uint32) hold the number of pairs
		binary.LittleEndian.PutUint32(b[8:12], uint32(len(m)))
		// bytes 12:16 (uint32) hold the size of the entire map for this inode
		binary.LittleEndian.PutUint32(b[12:16], uint32(len(single)))

		// add the lookupTable bytes
		lookupTable = append(lookupTable, b...)
		// add the actual metadata bytes
		buf = append(buf, single...)
		// the offset is moved forward
		offset += len(single)
		if len(buf) > maxSize {
			written, err := writeMetadataBlock(buf[:maxSize], f, compressor, location)
			if err != nil {
				return allWritten, 0, err
			}
			// count all we have written
			allWritten += written
			buf = buf[maxSize:]
			offset = offset - maxSize
			location += int64(written)
		}
	}
	// if there is anything left at the end
	if len(buf) > 0 {
		written, err := writeMetadataBlock(buf, f, compressor, location)
		if err != nil {
			return allWritten, 0, err
		}
		// count all we have written
		allWritten += written
		location += int64(written)
	}

	// hold the id table lookup
	var indexEntries []uint64

	// write the lookupTable - this too is stored as metadata blocks
	var i int
	for i = 0; i < len(lookupTable); i += maxSize {
		written, err := writeMetadataBlock(lookupTable[i*maxSize:i*maxSize+maxSize], f, compressor, location)
		if err != nil {
			return allWritten, 0, err
		}
		indexEntries = append(indexEntries, uint64(location))
		// count all we have written
		allWritten += written
		location += int64(written)
	}
	// was there any left?
	remainder := len(lookupTable) % maxSize
	if remainder > 0 {
		written, err := writeMetadataBlock(lookupTable[remainder:], f, compressor, location)
		if err != nil {
			return allWritten, 0, err
		}
		indexEntries = append(indexEntries, uint64(location))
		// count all we have written
		allWritten += written
		location += int64(written)
	}
	// finally, we need the ID table
	b := make([]byte, 16+8*len(indexEntries))
	binary.LittleEndian.PutUint64(b[0:8], uint64(initialLocation))
	binary.LittleEndian.PutUint32(b[8:12], uint32(len(lookupTable)))
	for _, e := range indexEntries {
		b2 := make([]byte, 8)
		binary.LittleEndian.PutUint64(b2, e)
		b = append(b, b2...)
	}

	// just write it out
	idTableLocation := location
	written, err := f.WriteAt(b, idTableLocation)
	if err != nil {
		return allWritten, 0, fmt.Errorf("error writing xattrs id index: %v", err)
	}
	allWritten += written

	return allWritten, uint64(idTableLocation), nil
}

func xAttrKeyConvert(key string) (uint16, string, error) {
	// get the prefix
	prefix := strings.SplitN(key, ".", 2)
	if len(prefix) != 2 {
		return 0, "", fmt.Errorf("invalid xattr key: %s", key)
	}
	var prefixID uint16
	switch prefix[0] {
	case "user":
		prefixID = 0
	case "trusted":
		prefixID = 1
	case "security":
		prefixID = 2
	default:
		return 0, "", fmt.Errorf("unknown xattr key: %s", key)
	}
	return prefixID, prefix[1], nil
}

func createInodes(fileList []*finalizeFileInfo, idtable map[uint32]uint16, options FinalizeOptions) ([]inode, error) {
	// get the inodes
	inodes := make([]inode, 0)
	var inodeIndex uint32

	// need to keep track of directory position in directory table
	// build our inodes for our files - must include all file types
	for _, e := range fileList {
		var (
			in     inodeBody
			inodeT inodeType
		)
		switch e.fileType {
		case fileRegular:
			/*
				use an extendedFile if any of the above is true:
				- startBlock (from beginning of data section) does not fit in uint32
				- fileSize does not fit in uint32
				- it is a sparse file
				- it has extended attributes
				- it has hard links
			*/
			if e.startBlock|uint32max != uint32max || e.Size()|int64(uint32max) != int64(uint32max) || len(e.xattrs) > 0 || e.links > 0 {
				// use extendedFile inode
				ef := &extendedFile{
					startBlock: e.startBlock,
					fileSize:   uint64(e.Size()),
					blockSizes: e.blocks,
					links:      e.links,
					xAttrIndex: e.xAttrIndex,
				}
				if e.fragment != nil {
					ef.fragmentBlockIndex = e.fragment.block
					ef.fragmentOffset = e.fragment.offset
				}
				in = ef
				inodeT = inodeExtendedFile
			} else {
				// use basicFile
				bf := &basicFile{
					startBlock: uint32(e.startBlock),
					fileSize:   uint32(e.Size()),
					blockSizes: e.blocks,
				}
				if e.fragment != nil {
					bf.fragmentBlockIndex = e.fragment.block
					bf.fragmentOffset = e.fragment.offset
				}
				in = bf
				inodeT = inodeBasicFile
			}
		case fileSymlink:
			/*
				use an extendedSymlink if it has extended attributes
				- startBlock (from beginning of data section) does not fit in uint32
				- fileSize does not fit in uint32
				- it is a sparse file
				- it has extended attributes
				- it has hard links
			*/
			target, err := os.Readlink(e.path)
			if err != nil {
				return inodes, fmt.Errorf("Unable to read target for symlink at %s: %v", e.path, err)
			}
			if len(e.xattrs) > 0 {
				in = &extendedSymlink{
					links:      e.links,
					target:     target,
					xAttrIndex: e.xAttrIndex,
				}
				inodeT = inodeExtendedSymlink
			} else {
				in = &basicSymlink{
					links:  e.links,
					target: target,
				}
				inodeT = inodeBasicSymlink
			}
		case fileDirectory:
			/*
				use an extendedDirectory if any of the following is true:
				- the directory itself has extended attributes
				- the size of the directory does not fit in a single metadata block, i.e. >8K uncompressed
				- it has more than 256 entries
			*/
			if e.startBlock|uint32max != uint32max || e.Size()|int64(uint32max) != int64(uint32max) || len(e.xattrs) > 0 || e.links > 0 {
				// use extendedFile inode
				in = &extendedDirectory{
					startBlock: uint32(e.startBlock),
					fileSize:   uint32(e.Size()),
					links:      e.links,
					xAttrIndex: e.xAttrIndex,
				}
				inodeT = inodeExtendedDirectory
			} else {
				// use basicFile
				in = &basicDirectory{
					startBlock: uint32(e.startBlock),
					links:      e.links,
					fileSize:   uint16(e.Size()),
				}
				inodeT = inodeBasicDirectory
			}
		case fileBlock:
			major, minor, err := getDeviceNumbers(e.path)
			if err != nil {
				return inodes, fmt.Errorf("Unable to read major/minor device numbers for block device at %s: %v", e.path, err)
			}
			if len(e.xattrs) > 0 {
				in = &extendedBlock{
					extendedDevice{
						links:      e.links,
						major:      major,
						minor:      minor,
						xAttrIndex: e.xAttrIndex,
					},
				}
				inodeT = inodeExtendedBlock
			} else {
				in = &basicBlock{
					basicDevice{
						links: e.links,
						major: major,
						minor: minor,
					},
				}
				inodeT = inodeBasicBlock
			}
		case fileChar:
			major, minor, err := getDeviceNumbers(e.path)
			if err != nil {
				return inodes, fmt.Errorf("Unable to read major/minor device numbers for char device at %s: %v", e.path, err)
			}
			if len(e.xattrs) > 0 {
				in = &extendedChar{
					extendedDevice{
						links:      e.links,
						major:      major,
						minor:      minor,
						xAttrIndex: e.xAttrIndex,
					},
				}
				inodeT = inodeExtendedChar
			} else {
				in = &basicChar{
					basicDevice{
						links: e.links,
						major: major,
						minor: minor,
					},
				}
				inodeT = inodeBasicChar
			}
		case fileFifo:
			if len(e.xattrs) > 0 {
				in = &extendedFifo{
					extendedIPC{
						links:      e.links,
						xAttrIndex: e.xAttrIndex,
					},
				}
				inodeT = inodeExtendedFifo
			} else {
				in = &basicFifo{
					basicIPC{
						links: e.links,
					},
				}
				inodeT = inodeBasicFifo
			}
		case fileSocket:
			if len(e.xattrs) > 0 {
				in = &extendedSocket{
					extendedIPC{
						links:      e.links,
						xAttrIndex: e.xAttrIndex,
					},
				}
				inodeT = inodeExtendedSocket
			} else {
				in = &basicSocket{
					basicIPC{
						links: e.links,
					},
				}
				inodeT = inodeBasicSocket
			}
		}
		// set the uid and gid
		uid := e.uid
		gid := e.gid
		if options.FileUID != nil {
			uid = *options.FileUID
		}
		if options.FileGID != nil {
			gid = *options.FileGID
		}
		// get index to the uid and gid
		uidIdx := getTableIdx(idtable, uid)
		gidIdx := getTableIdx(idtable, gid)
		e.inode = &inodeImpl{
			header: &inodeHeader{
				inodeType: inodeT,
				modTime:   e.ModTime(),
				mode:      e.Mode(),
				uidIdx:    uidIdx,
				gidIdx:    gidIdx,
				index:     inodeIndex,
			},
			body: in,
		}
		inodes = append(inodes, e.inode)
		inodeIndex++
	}

	return inodes, nil
}

func createDirectoryData(fileList []*finalizeFileInfo, ws string) ([]byte, error) {
	directories := make([]byte, 0)
	for _, f := range fileList {
		// only process directories
		if !f.IsDir() {
			continue
		}

		// each directory entry needs to point to its children on disk
		// the reverse direction is in directory.go:parseDirectory()
		//  there it reads the raw data; we need to do the reverse - for each directory, create the raw data
		//  look there, it consists of a header and one or more entries
		//  remember that the common information is moved to the header, while unique data
		//     per directory entry is in the entry. This saves space.

	}

	return directories, nil
}

// dirMapToList convert the map of directories to a list. The list should
// be sorted with directories in any order, given that root "." is first,
// and within a directory, sorted "asciibetically".
// Typically, all children of a given directory have sequential inode numbers.
// Our sorting should do this already. However, we could improve the algorithm.
func dirMapToList(dirMap map[string]*finalizeFileInfo) []*finalizeFileInfo {
	// add the depth to each one
	root := dirMap["."]
	root.addProperties(1)

	list := make([]*finalizeFileInfo, 0, len(dirMap))
	for _, v := range dirMap {
		// we already did root
		if !v.isRoot {
			list = append(list, v)
		}
	}

	return list
}

// extractXattrs take all of the extended attributes on the finalizeFileInfo
// and write them out. Returns a slice of all unique xattr key-value pairs.
func extractXattrs(list []*finalizeFileInfo) []map[string]string {
	var (
		xattrs   []map[string]string
		indexMap = map[string]int{}
	)
	for _, e := range list {
		if len(e.xattrs) == 0 {
			continue
		}
		var (
			index int
			key   = hashStringMap(e.xattrs)
		)
		if pos, ok := indexMap[key]; ok {
			// reference already-existing duplicates
			index = pos
		} else {
			index = len(xattrs)
			xattrs = append(xattrs, e.xattrs)
			// save the unique combination
			indexMap[key] = index
		}
		e.xAttrIndex = uint32(index)
	}
	return xattrs
}

// hashStringMap make a unique hash out of a string map, to make it easy to compare
func hashStringMap(m map[string]string) string {
	// simple algorithm is good enough for this
	// just join all of the key-value pairs with =, and separate with ;, so you get
	//  key1=value1;key2=value2;...
	// it isn't perfect, but it doesn't have to be
	var pairs []string
	for k, v := range m {
		pairs = append(pairs, fmt.Sprintf("%s=%s", k, v))
	}
	return strings.Join(pairs, ";")
}

// fragmentBlock size and compression of a single fragment block
type fragmentBlock struct {
	size       uint32
	compressed bool
	location   int64
}

// blockPosition position of something inside a data or metadata section.
// Includes the block number relative to the start, and the offset within
// the block.
type blockPosition struct {
	block  uint32
	offset uint16
}

// createDirectories take a list of finalizeFileInfo, turn it into a slice of
// []directory.
func createDirectories(e *finalizeFileInfo, inodeLocations []blockPosition) []*directory {
	dirs := make([]*directory, 0)
	entries := make([]*directoryEntryRaw, 0)
	// go through each entry, and create a directory structure for it
	// we will cycle through each directory, creating an entry for it
	// and its children. A second pass will split into headers
	for _, child := range e.children {
		index := child.inode.index()
		blockPos := inodeLocations[index]
		entry := &directoryEntryRaw{
			name:           child.Name(),
			isSubdirectory: !child.isRoot,
			startBlock:     blockPos.block,
			offset:         blockPos.offset,
			// we do not yet know the inodeNumber, which is an offset from the one in the header
			// it will be filled in later
		}
		entries = append(entries, entry)
	}
	dir := &directory{
		entries: entries,
	}
	dirs = append(dirs, dir)
	// do children in a separate loop, so that we get all of the children lined up
	for _, child := range e.children {
		if child.IsDir() {
			dirs = append(dirs, createDirectories(child, inodeLocations)...)
		}
	}
	return dirs
}

// optimizeDirectoryTable convert a slice of directoryEntryRaw into a []directory
// that can be written to disk
func optimizeDirectoryTable(directories []*directory) []*directory {
	// each directory is just a list of directoryEntryRaw; pull out the common
	// elements for each into a header.
	dirs := make([]*directory, 0)
	for _, d := range directories {
		dirs = append(dirs, d)
	}
	return dirs
}

// getInodeLocations get a map of each inode index and where it will be on disk
// i.e. the inode block, and the offset into the block
func getInodeLocations(inodes []inode) []blockPosition {
	// keeps our reference
	positions := make([]blockPosition, 0, len(inodes))
	var pos int64

	// get block position for each inode
	for _, i := range inodes {
		b := i.toBytes()
		positions = append(positions, blockPosition{
			block:  uint32(pos / metadataBlockSize),
			offset: uint16(pos % metadataBlockSize),
		})
		pos += int64(len(b))
	}

	return positions
}

// getDirectoryLocations get a map of each directory index and where it will be
// on disk i.e. the directory block, and the offset into the block
func getDirectoryLocations(directories []*directory) []blockPosition {
	// keeps our reference
	refTable := make([]blockPosition, 0, len(directories))
	pos := 0

	// get block position for each inode
	for _, d := range directories {
		// we start without knowing the inode block/number
		// in any case, this func is just here to give us sizes and therefore
		// locations inside the directory metadata blocks, not actual writable
		// bytes
		b := d.toBytes(0, 0)
		refTable = append(refTable, blockPosition{
			block:  uint32(pos / int(metadataBlockSize)),
			offset: uint16(pos % int(metadataBlockSize)),
		})
		pos += len(b)
	}

	return refTable
}

// updateInodesFromDirectories update the blockPosition for each directory
// inode.
func updateInodesFromDirectories(inodes []inode, dirTable []*directory, dirLocations []blockPosition) error {
	// go through each directory, find its inode, and update it with the
	// correct block and offset
	for i, d := range dirTable {
		index := d.inodeIndex
		in := inodes[index]
		inBody := in.getBody()
		switch inBody.(type) {
		case *basicDirectory:
			dir := inBody.(*basicDirectory)
			dir.startBlock = dirLocations[i].block
			dir.offset = dirLocations[i].offset
		case *extendedDirectory:
			dir := inBody.(*extendedDirectory)
			dir.startBlock = dirLocations[i].block
			dir.offset = dirLocations[i].offset
		default:
			return fmt.Errorf("inode at index %d from directory at index %d was unexpected type", index, i)
		}
	}
	return nil
}
