# Copyright 2017 Reswitched Team
#
# Permission to use, copy, modify, and/or distribute this software for any purpose with or
# without fee is hereby granted, provided that the above copyright notice and this permission
# notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS
# SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL
# THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY
# DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF
# CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE
# OR PERFORMANCE OF THIS SOFTWARE.

# nxo64.py: IDA loader (and library for reading nso/nro files)

from __future__ import print_function

import gzip, hashlib, math, os, re, struct, sys
from struct import unpack as up, pack as pk

from io import BytesIO

import lz4.block

uncompress = lz4.block.decompress

if sys.version_info[0] == 3:
    iter_range = range
    int_types = (int,)
    ascii_string = lambda b: b.decode('ascii')
    bytes_to_list = lambda b: list(b)
    list_to_bytes = lambda l: bytes(l)
else:
    iter_range = xrange
    int_types = (int, long)
    ascii_string = lambda b: str(b)
    bytes_to_list = lambda b: map(ord, b)
    list_to_bytes = lambda l: ''.join(map(chr, l))

def kip1_blz_decompress(compressed):
    compressed_size, init_index, uncompressed_addl_size = struct.unpack('<III', compressed[-0xC:])
    # BLZ allows "partial compression": the first len - compressed_size bytes
    # are stored raw and the stream only encodes the rest, so decoding must
    # stop at that prefix boundary, not at offset 0 (17.0.1 spl.kip1 .text
    # carries a 21-byte raw prefix; decoding past it exhausts the stream).
    prefix_len = len(compressed) - compressed_size
    decompressed = compressed[:] + b'\x00' * uncompressed_addl_size
    decompressed_size = len(decompressed)
    if len(compressed) != compressed_size:
        assert len(compressed) > compressed_size
        compressed = compressed[prefix_len:]
    if not (compressed_size + uncompressed_addl_size):
        return b''
    compressed = bytes_to_list(compressed)
    decompressed = bytes_to_list(decompressed)
    index = compressed_size - init_index
    outindex = decompressed_size
    while outindex > prefix_len:
        index -= 1
        control = compressed[index]
        for i in iter_range(8):
            if control & 0x80:
                if index < 2:
                    raise ValueError('Compression out of bounds!')
                index -= 2
                segmentoffset = compressed[index] | (compressed[index+1] << 8)
                segmentsize = ((segmentoffset >> 12) & 0xF) + 3
                segmentoffset &= 0x0FFF
                segmentoffset += 2
                # the match size field bottoms out at 3, so a match may claim
                # more bytes than remain to fill; clamp like LibHac's
                # KipReader.DecompressBlz instead of treating it as corruption
                if segmentsize > outindex - prefix_len:
                    segmentsize = outindex - prefix_len
                for j in iter_range(segmentsize):
                    if outindex + segmentoffset >= decompressed_size:
                        raise ValueError('Compression out of bounds!')
                    data = decompressed[outindex+segmentoffset]
                    outindex -= 1
                    decompressed[outindex] = data
            else:
                if outindex < 1:
                    raise ValueError('Compression out of bounds!')
                outindex -= 1
                index -= 1
                decompressed[outindex] = compressed[index]
            control <<= 1
            control &= 0xFF
            if outindex <= prefix_len:
                break
    return list_to_bytes(decompressed)

class BinFile(object):
    def __init__(self, li):
        self._f = li

    def read(self, arg):
        if isinstance(arg, str):
            fmt = '<' + arg
            size = struct.calcsize(fmt)
            raw = self._f.read(size)
            out = struct.unpack(fmt, raw)
            if len(out) == 1:
                return out[0]
            return out
        elif arg is None:
            return self._f.read()
        else:
            out = self._f.read(arg)
            return out

    def read_from(self, arg, offset):
        old = self.tell()
        try:
            self.seek(offset)
            out = self.read(arg)
        finally:
            self.seek(old)
        return out

    def seek(self, off):
        self._f.seek(off)

    def close(self):
        self._f.close()

    def tell(self):
        return self._f.tell()


(DT_NULL, DT_NEEDED, DT_PLTRELSZ, DT_PLTGOT, DT_HASH, DT_STRTAB, DT_SYMTAB, DT_RELA, DT_RELASZ,
 DT_RELAENT, DT_STRSZ, DT_SYMENT, DT_INIT, DT_FINI, DT_SONAME, DT_RPATH, DT_SYMBOLIC, DT_REL,
 DT_RELSZ, DT_RELENT, DT_PLTREL, DT_DEBUG, DT_TEXTREL, DT_JMPREL, DT_BIND_NOW, DT_INIT_ARRAY,
 DT_FINI_ARRAY, DT_INIT_ARRAYSZ, DT_FINI_ARRAYSZ, DT_RUNPATH, DT_FLAGS) = iter_range(31)
DT_GNU_HASH = 0x6ffffef5
DT_VERSYM = 0x6ffffff0
DT_RELACOUNT = 0x6ffffff9
DT_RELCOUNT = 0x6ffffffa
DT_FLAGS_1 = 0x6ffffffb
DT_VERDEF = 0x6ffffffc
DT_VERDEFNUM = 0x6ffffffd

# DT_RELRSZ / DT_RELR / DT_RELRENT (35/36/37): gABI "compact relative
# relocations". 17.0.1+ firmware NSOs are static PIE with no DT_RELA at all;
# every R_AARCH64_RELATIVE fixup is packed into this bitmap table instead.
DT_RELRSZ = 35
DT_RELR = 36
DT_RELRENT = 37

STT_NOTYPE = 0
STT_OBJECT = 1
STT_FUNC = 2
STT_SECTION = 3

STB_LOCAL = 0
STB_GLOBAL = 1
STB_WEAK = 2

STV_DEFAULT = 0
STV_INTERNAL = 1
STV_HIDDEN = 2
STV_PROTECTED = 3

R_ARM_ABS32 = 2
R_ARM_TLS_DESC = 13
R_ARM_GLOB_DAT = 21
R_ARM_JUMP_SLOT = 22
R_ARM_RELATIVE = 23
R_ARM_IRELATIVE = 160

R_AARCH64_ABS64 = 257
R_AARCH64_GLOB_DAT = 1025
R_AARCH64_JUMP_SLOT = 1026
R_AARCH64_RELATIVE = 1027
R_AARCH64_TLSDESC = 1031
R_AARCH64_IRELATIVE = 1032

MULTIPLE_DTS = set([DT_NEEDED])


class Range(object):
    def __init__(self, start, size):
        self.start = start
        self.size = size
        self.end = start+size
        self._inclend = start+size-1

    def overlaps(self, other):
        return self.start <= other._inclend and other.start <= self._inclend

    def includes(self, other):
        return other.start >= self.start and other._inclend <= self._inclend

    def __repr__(self):
        return 'Range(0x%X -> 0x%X)' % (self.start, self.end)


class Segment(object):
    def __init__(self, r, name, kind):
        self.range = r
        self.name = name
        self.kind = kind
        self.sections = []

    def add_section(self, s):
        for i in self.sections:
            assert not i.range.overlaps(s.range), '%r overlaps %r' % (s, i)
        self.sections.append(s)


class Section(object):
    def __init__(self, r, name):
        self.range = r
        self.name = name

    def __repr__(self):
        return 'Section(%r, %r)' % (self.range, self.name)


def suffixed_name(name, suffix):
    if suffix == 0:
        return name
    return '%s.%d' % (name, suffix)


class SegmentBuilder(object):
    def __init__(self):
        self.segments = []

    def add_segment(self, start, size, name, kind):
        r = Range(start, size)
        for i in self.segments:
            assert not r.overlaps(i.range)
        self.segments.append(Segment(r, name, kind))

    def add_section(self, name, start, end=None, size=None):
        assert end is None or size is None
        if size == 0:
            return
        if size is None:
            size = end-start
        r = Range(start, size)
        for i in self.segments:
            if i.range.includes(r):
                i.add_section(Section(r, name))
                return
        assert False, "no containing segment for %r" % (name,)

    def flatten(self):
        self.segments.sort(key=lambda s: s.range.start)
        parts = []
        for segment in self.segments:
            suffix = 0
            segment.sections.sort(key=lambda s: s.range.start)
            pos = segment.range.start
            for section in segment.sections:
                if pos < section.range.start:
                    parts.append((pos, section.range.start, suffixed_name(segment.name, suffix), segment.kind))
                    suffix += 1
                    pos = section.range.start
                parts.append((section.range.start, section.range.end, section.name, segment.kind))
                pos = section.range.end
            if pos < segment.range.end:
                parts.append((pos, segment.range.end, suffixed_name(segment.name, suffix), segment.kind))
                suffix += 1
                pos = segment.range.end
        return parts


class ElfSym(object):
    def __init__(self, name, info, other, shndx, value, size):
        self.name = name
        self.shndx = shndx
        self.value = value
        self.size = size

        self.vis = other & 3
        self.type = info & 0xF
        self.bind = info >> 4

    def __repr__(self):
        return 'Sym(name=%r, shndx=0x%X, value=0x%X, size=0x%X, vis=%r, type=%r, bind=%r)' % (
            self.name, self.shndx, self.value, self.size, self.vis, self.type, self.bind)


class NxoFileBase(object):
    # 32-byte header module id (the "Build ID" emulators match mods and
    # cheats against); overridden by NsoFile/NroFile, absent from KIP1.
    # Class-level default so subclass __init__ order doesn't matter.
    module_id = None

    # DT_SONAME from .dynamic: the module's own rtld-visible name (e.g.
    # firmware hid -> "hid.nss").  Parsed in __init__; None when the tag is
    # absent (game mains/subsdkX and homebrew NROs typically carry none).
    soname = None

    # KIP1-only header identity/scheduling fields (offsets per LibHac
    # KipHeader.cs), set by KipFile before super().__init__().
    kip_name = None
    kip_program_id = None
    kip_version = None
    kip_priority = None
    kip_core = None
    kip_stack_size = None

    # nnSdk ModuleVersion triplet (major, minor, micro) behind the rocrt
    # pointer at image start +8; set by __init__ itself.  None on older
    # SDKs (BotW-era games) which carry their SDK identity in the
    # .api_info strings instead.
    sdk_version = None
    sdk_offset = None

    # .api_info extent (module-relative offset, size), read from the
    # format header (NSO 0x88 / NRO 0x68, rodata-relative as produced) by
    # NsoFile/NroFile before super().__init__().  None when the producer
    # left it empty (17.x firmware and homebrew NROs).
    api_info = None
    api_components = None

    # Pre-dynamic-linking homebrew NROs (libnx before mid-2018, e.g.
    # ChoiDujourNX v1.0.1) carry no ModuleHeader at all: NroStart's +4
    # MOD0-offset field is 0 and the whole rtld layer (.dynamic, .dynsym,
    # relocations, imports/exports) simply does not exist -- the NRO
    # header alone describes the image.  When set, NxoFileBase falls back
    # to header-only loading for such files; for NSO/KIP a missing MOD0
    # means corruption and stays a hard error.  Set by NroFile before
    # super().__init__() (same pattern as the kip_* fields).
    allow_no_mod0 = False

    # segment = (content, file offset, vaddr, vsize)
    def __init__(self, text, ro, data, bsssize):
        self.text = text
        self.ro = ro
        self.data = data
        self.bsssize = bsssize
        self.textoff = text[2]
        self.textsize = text[3]
        self.rodataoff = ro[2]
        self.rodatasize = ro[3]
        self.dataoff = data[2]
        flatsize = data[2] + data[3]
        
        full = text[0]
        if ro[2] >= len(full):
            full += b'\x00' * (ro[2] - len(full))
        else:
            print('truncating .text?')
            full = full[:ro[2]]
        full += ro[0]
        if data[2] > len(full):
            full += b'\x00' * (data[2] - len(full))
        else:
            print('truncating .rodata?')
        full += data[0]
        f = BinFile(BytesIO(full))

        self.binfile = f

        # read MOD
        self.modoff = f.read_from('I', 4)

        self.isLibnx = False
        if self.allow_no_mod0 and self.modoff == 0:
            # Header-only NRO (see allow_no_mod0): segment bounds come
            # straight from the NRO header -- .data runs to the end of the
            # declared image and .bss follows it with no gap, which is
            # exactly what real MOD0 NROs declare (gsl: .data ends at
            # 0x3ec68 == image end).  bsssize keeps the header value
            # passed in (0x38, corrected in 3ad2a24 for this case).
            self.modoff = None
            self.datasize = data[3]
            self.bssoff = flatsize
            self.armv7 = False  # homebrew NROs are aarch64-only
            self.offsize = 8
            self.dynamic = dynamic = {i: [] for i in MULTIPLE_DTS}
            self.dynstr = b'\x00'
            print('note: no MOD0 header, loading as pre-dynamic-linking homebrew NRO')
            has_mod0 = False
        else:
            f.seek(self.modoff)
            if f.read('4s') != b'MOD0':
                raise NxoException('invalid MOD0 magic')

            self.dynamicoff = self.modoff + f.read('i')
            self.bssoff     = self.modoff + f.read('i')
            self.bssend     = self.modoff + f.read('i')
            self.unwindoff  = self.modoff + f.read('i')
            self.unwindend  = self.modoff + f.read('i')
            self.moduleoff  = self.modoff + f.read('i')


            self.datasize = self.bssoff - self.dataoff
            self.bsssize = self.bssend - self.bssoff

            if f.read('4s') == 'LNY0':
                self.isLibnx = True
                self.libnx_got_start    = self.modoff + f.read('i')
                self.libnx_got_end      = self.modoff + f.read('i')

            # rocrt places a branch at the image start, then two pointers:
            # +4 is the ModuleHeader/MOD0 offset consumed above, +8 points
            # at the 12-byte nnSdk ModuleVersion (major, minor, micro; on
            # 17.0.0+ it sits right after the ModuleHeader -- the pointer
            # stays authoritative).  Older SDKs emit neither branch nor
            # pointer (their SDK identity is the .api_info string table
            # parsed below), so guard on the branch opcode and
            # sanity-check the triplet like nso2elf.  Pre-dynamic
            # homebrew NROs are never nnSdk and skip this entirely
            # (ChoiDujourNX's +8 holds the "HOMEBREW" marker).
            entry = f.read_from('I', 0)
            if entry == 1 or (entry >> 26) == 5:
                sdkoff = f.read_from('i', 8)
                if 0 < sdkoff < flatsize - 12:
                    major, minor, micro = f.read_from('III', sdkoff)
                    if 0 < major < 1000 and 0 <= minor < 1000 and 0 <= micro < 1000:
                        self.sdk_version = (major, minor, micro)
                        self.sdk_offset = sdkoff
            has_mod0 = True

        self.segment_builder = builder = SegmentBuilder()
        for off,sz,name,kind in [
            (self.textoff, self.textsize, ".text", "CODE"),
            (self.rodataoff, self.rodatasize, ".rodata", "CONST"),
            (self.dataoff, self.datasize, ".data", "DATA"),
            (self.bssoff, self.bsssize, ".bss", "BSS"),
        ]:
            builder.add_segment(off, sz, name, kind)

        # read dynamic
        if has_mod0:
            self.armv7 = (f.read_from('Q', self.dynamicoff) > 0xFFFFFFFF or f.read_from('Q', self.dynamicoff+0x10) > 0xFFFFFFFF)
            self.offsize = 4 if self.armv7 else 8

            f.seek(self.dynamicoff)
            self.dynamic = dynamic = {}
            for i in MULTIPLE_DTS:
                dynamic[i] = []
            for i in iter_range((flatsize - self.dynamicoff) // 0x10):
                tag, val = f.read('II' if self.armv7 else 'QQ')
                if tag == DT_NULL:
                    break
                if tag in MULTIPLE_DTS:
                    dynamic[tag].append(val)
                else:
                    dynamic[tag] = val
            builder.add_section('.dynamic', self.dynamicoff, end=f.tell())

            # read .dynstr
            if DT_STRTAB in dynamic and DT_STRSZ in dynamic:
                f.seek(dynamic[DT_STRTAB])
                self.dynstr = f.read(dynamic[DT_STRSZ])
            else:
                self.dynstr = b'\x00'
                print('warning: no dynstr')

            for startkey, szkey, name in [
                (DT_STRTAB, DT_STRSZ, '.dynstr'),
                (DT_INIT_ARRAY, DT_INIT_ARRAYSZ, '.init_array'),
                (DT_FINI_ARRAY, DT_FINI_ARRAYSZ, '.fini_array'),
                (DT_RELA, DT_RELASZ, '.rela.dyn'),
                (DT_RELR, DT_RELRSZ, '.relr.dyn'),
                (DT_REL, DT_RELSZ, '.rel.dyn'),
                (DT_JMPREL, DT_PLTRELSZ, ('.rel.plt' if self.armv7 else '.rela.plt')),
            ]:
                if startkey in dynamic and szkey in dynamic:
                    builder.add_section(name, dynamic[startkey], size=dynamic[szkey])

        # rocrt/SDK metadata sections: the module header this loader itself
        # consumes (0x1C covers every field read on pre-19.0 layouts), the
        # nnSdk version triplet behind the +8 pointer, and the .api_info
        # extent -- older SDKs fill it with NUL-terminated component
        # descriptors like "SDK MW+Nintendo+NintendoWare_G3d-4_4_0-Release".
        if has_mod0:
            builder.add_section('.mod0', self.modoff, size=0x1C)
        if self.sdk_offset is not None:
            builder.add_section('.nnsdk', self.sdk_offset, size=12)
        if self.api_info:
            api_off, api_size = self.api_info
            builder.add_section('.api_info', api_off, size=api_size)
            self.api_components = [ascii_string(s) for s in f.read_from('%ds' % api_size, api_off).split(b'\x00') if s]

        self.needed = [self.get_dynstr(i) for i in self.dynamic[DT_NEEDED]]

        # DT_SONAME (single-entry tag): offset into .dynstr naming this
        # module itself -- the name other modules' DT_NEEDED entries
        # resolve against.
        self.soname = self.get_dynstr(self.dynamic[DT_SONAME]) if DT_SONAME in self.dynamic else None

        # load .dynsym
        self.symbols = symbols = []
        if DT_SYMTAB in dynamic and DT_STRTAB in dynamic:
            f.seek(dynamic[DT_SYMTAB])
            while True:
                if dynamic[DT_SYMTAB] < dynamic[DT_STRTAB] and f.tell() >= dynamic[DT_STRTAB]:
                    break
                if self.armv7:
                    st_name, st_value, st_size, st_info, st_other, st_shndx = f.read('IIIBBH')
                else:
                    st_name, st_info, st_other, st_shndx, st_value, st_size = f.read('IBBHQQ')
                if st_name >= len(self.dynstr):
                    break
                symbols.append(ElfSym(self.get_dynstr(st_name), st_info, st_other, st_shndx, st_value, st_size))
            builder.add_section('.dynsym', dynamic[DT_SYMTAB], end=f.tell())

        self.plt_entries = []
        self.relocations = []
        locations = set()
        plt_got_end = None
        if DT_REL in dynamic and DT_RELSZ in dynamic:
            locations |= self.process_relocations(f, symbols, dynamic[DT_REL], dynamic[DT_RELSZ])

        if DT_RELA in dynamic and DT_RELASZ in dynamic:
            locations |= self.process_relocations(f, symbols, dynamic[DT_RELA], dynamic[DT_RELASZ])

        # Compact relative relocations (DT_RELR, gABI). 17.0.1+ firmware modules
        # ship no DT_RELA: every R_AARCH64_RELATIVE fixup is packed into a u64
        # bitmap table in .rodata instead:
        #   even word (bit0 = 0): address entry -- relocate the qword at that
        #     module-relative address, then where = entry + 8
        #   odd word (bit0 = 1): bitmap entry -- bit i (i = 0..62, bit0 is the
        #     tag) relocates where + 8*i; afterwards where += 63*8, so chained
        #     bitmaps keep walking forward through .data
        # Entries carry no addend field: the link-time value already stored at
        # the target is the implicit addend (runtime semantic: *target += base).
        # Expand each target into a regular R_AARCH64_RELATIVE entry so the
        # existing apply loop fixes the value, marks .text targets as functions
        # and turns them into offsets/xrefs. read_from() restores the file
        # position, so it does not disturb the sequential walk of the table.
        if DT_RELR in dynamic and DT_RELRSZ in dynamic:
            if self.armv7:
                print('warning: ignoring DT_RELR in armv7 module')
            elif DT_RELRENT in dynamic and dynamic[DT_RELRENT] != 8:
                print('warning: ignoring DT_RELR with entsize != 8')
            else:
                where = 0
                f.seek(dynamic[DT_RELR])
                for i in iter_range(dynamic[DT_RELRSZ] // 8):
                    entry = f.read('Q')
                    if (entry & 1) == 0:
                        self.relocations.append((entry, R_AARCH64_RELATIVE, None, f.read_from('Q', entry)))
                        where = entry + 8
                    elif where:
                        for j in iter_range(63):
                            if entry & (2 << j):
                                target = where + j * 8
                                self.relocations.append((target, R_AARCH64_RELATIVE, None, f.read_from('Q', target)))
                        where += 63 * 8
                    else:
                        print('warning: DT_RELR bitmap entry before any address entry')
                        break

        if DT_JMPREL in dynamic and DT_PLTRELSZ in dynamic:
            pltlocations = self.process_relocations(f, symbols, dynamic[DT_JMPREL], dynamic[DT_PLTRELSZ])
            locations |= pltlocations

            plt_got_start = min(pltlocations)
            plt_got_end = max(pltlocations) + self.offsize
            if DT_PLTGOT in dynamic:
                builder.add_section('.got.plt', dynamic[DT_PLTGOT], end=plt_got_end)

            if not self.armv7:
                f.seek(0)
                text = f.read(self.textsize)
                last = 12
                while True:
                    pos = text.find(struct.pack('<I', 0xD61F0220), last)
                    if pos == -1: break
                    last = pos+1
                    if (pos % 4) != 0: continue
                    off = pos - 12
                    a, b, c, d = struct.unpack_from('<IIII', text, off)
                    if d == 0xD61F0220 and (a & 0x9f00001f) == 0x90000010 and (b & 0xffe003ff) == 0xf9400211:
                        base = off & ~0xFFF
                        immhi = (a >> 5) & 0x7ffff
                        immlo = (a >> 29) & 3
                        paddr = base + ((immlo << 12) | (immhi << 14))
                        poff = ((b >> 10) & 0xfff) << 3
                        target = paddr + poff
                        if plt_got_start <= target < plt_got_end:
                            self.plt_entries.append((off, target))
                if self.plt_entries:
                    builder.add_section('.plt', min(self.plt_entries)[0], end=max(self.plt_entries)[0] + 0x10)

            # try to find the ".got" which should follow the ".got.plt"
            if not self.isLibnx:
                if plt_got_end is not None:
                    good = False
                    got_end = plt_got_end + self.offsize
                    while got_end in locations and (DT_INIT_ARRAY not in dynamic or got_end < dynamic[DT_INIT_ARRAY]):
                        good = True
                        got_end += self.offsize

                    if good:
                        builder.add_section('.got', plt_got_end, end=got_end)
        if self.isLibnx:
            builder.add_section('.got', self.libnx_got_start, end=self.libnx_got_end)

        self.sections = []
        for start, end, name, kind in builder.flatten():
            self.sections.append((start, end, name, kind))


    def process_relocations(self, f, symbols, offset, size):
        locations = set()
        f.seek(offset)
        relocsize = 8 if self.armv7 else 0x18
        for i in iter_range(size // relocsize):
            # NOTE: currently assumes all armv7 relocs have no addends,
            # and all 64-bit ones do.
            if self.armv7:
                offset, info = f.read('II')
                addend = None
                r_type = info & 0xff
                r_sym = info >> 8
            else:
                offset, info, addend = f.read('QQq')
                r_type = info & 0xffffffff
                r_sym = info >> 32

            sym = symbols[r_sym] if r_sym != 0 else None

            if r_type != R_AARCH64_TLSDESC and r_type != R_ARM_TLS_DESC:
                locations.add(offset)
            self.relocations.append((offset, r_type, sym, addend))
        return locations

    def get_dynstr(self, o):
        return ascii_string(self.dynstr[o:self.dynstr.index(b'\x00', o)])


class NsoFile(NxoFileBase):
    def __init__(self, fileobj):
        f = BinFile(fileobj)

        if f.read_from('4s', 0) != b'NSO0':
            raise NxoException('Invalid NSO magic')

        flags = f.read_from('I', 0xC)
        self.module_id = f.read_from('32s', 0x40)

        toff, tloc, tsize = f.read_from('III', 0x10)
        roff, rloc, rsize = f.read_from('III', 0x20)
        doff, dloc, dsize = f.read_from('III', 0x30)

        tfilesize, rfilesize, dfilesize = f.read_from('III', 0x60)
        bsssize = f.read_from('I', 0x3C)

        # .api_info extent at 0x88 (LibHac ApiInfoOffset/Size, switchbrew
        # EmbeddedOffset/Size), relative to .rodata: populated by older
        # SDKs, zeroed on 17.x firmware.
        api_off, api_size = f.read_from('II', 0x88)
        self.api_info = (rloc + api_off, api_size) if api_size else None

        print('load text: ')
        text = (uncompress(f.read_from(tfilesize, toff), uncompressed_size=tsize), None, tloc, tsize) if flags & 1 else (f.read_from(tsize, toff), toff, tloc, tsize)
        ro   = (uncompress(f.read_from(rfilesize, roff), uncompressed_size=rsize), None, rloc, rsize) if flags & 2 else (f.read_from(rsize, roff), roff, rloc, rsize)
        data = (uncompress(f.read_from(dfilesize, doff), uncompressed_size=dsize), None, dloc, dsize) if flags & 4 else (f.read_from(dsize, doff), doff, dloc, dsize)

        # Segment SHA-256 sanity check: flags bits 3/4/5 (one per segment)
        # mark the 32-byte hashes at 0xA0/0xC0/0xE0 as meaningful, and they
        # cover the *decompressed* bytes (same semantics as LibHac's
        # NsoReader).  Warn on mismatch but keep loading -- a partially
        # corrupt module is often still worth analyzing.
        for seg, name, bit, hoff in ((text, '.text', 8, 0xA0), (ro, '.ro', 16, 0xC0), (data, '.data', 32, 0xE0)):
            if flags & bit:
                want = f.read_from('32s', hoff)
                got = hashlib.sha256(seg[0]).digest()
                if got != want:
                    print('warning: %s sha256 mismatch (header %s, actual %s)'
                          % (name,
                             ''.join('%02x' % c for c in bytes_to_list(want)),
                             ''.join('%02x' % c for c in bytes_to_list(got))))

        super(NsoFile, self).__init__(text, ro, data, bsssize)


class NroFile(NxoFileBase):
    def __init__(self, fileobj):
        f = BinFile(fileobj)

        if f.read_from('4s', 0x10) != b'NRO0':
            raise NxoException('Invalid NRO magic')

        f.seek(0x20)

        tloc, tsize = f.read('II')
        rloc, rsize = f.read('II')
        dloc, dsize = f.read('II')
        bsssize = f.read_from('I', 0x38)
        self.module_id = f.read_from('32s', 0x40)

        # .api_info extent at 0x68, the NRO counterpart of the NSO 0x88
        # pair (rodata-relative).  nnSdk-built NROs only; libnx leaves it
        # zero, so homebrew never carves the section.
        emb_off, emb_size = f.read_from('II', 0x68)
        self.api_info = (rloc + emb_off, emb_size) if emb_size else None

        text = (f.read_from(tsize, tloc), tloc, tloc, tsize)
        ro   = (f.read_from(rsize, rloc), rloc, rloc, rsize)
        data = (f.read_from(dsize, dloc), dloc, dloc, dsize)

        # pre-dynamic-linking homebrew NROs carry no ModuleHeader; see
        # allow_no_mod0 in NxoFileBase
        self.allow_no_mod0 = True

        super(NroFile, self).__init__(text, ro, data, bsssize)

class KipFile(NxoFileBase):
    def __init__(self, fileobj):
        f = BinFile(fileobj)

        if f.read_from('4s', 0) != b'KIP1':
            raise NxoException('Invalid KIP magic')

        # identity / scheduling fields (KipHeader.cs: Name@0x04 is 12 bytes,
        # so longer names arrive truncated, e.g. "ProcessMana")
        self.kip_name = f.read_from('12s', 0x4).split(b'\x00', 1)[0].decode('ascii', 'replace')
        self.kip_program_id = f.read_from('Q', 0x10)
        self.kip_version = f.read_from('i', 0x18)
        self.kip_priority = f.read_from('b', 0x1C)
        self.kip_core = f.read_from('b', 0x1D)

        flags = f.read_from('b', 0x1F)
            
        tloc, tsize, tfilesize = f.read_from('III', 0x20)
        rloc, rsize, rfilesize = f.read_from('III', 0x30)
        dloc, dsize, dfilesize = f.read_from('III', 0x40)
        
        toff = 0x100
        roff = toff + tfilesize
        doff = roff + rfilesize

        bsssize = f.read_from('I', 0x54)
        self.kip_stack_size = f.read_from('I', 0x3C)
        print('bss size 0x%x' % bsssize)

        print('load segments')
        text = (kip1_blz_decompress(f.read_from(tfilesize, toff)), None, tloc, tsize) if flags & 1 else (f.read_from(tfilesize, toff), toff, tloc, tsize)
        ro   = (kip1_blz_decompress(f.read_from(rfilesize, roff)), None, rloc, rsize) if flags & 2 else (f.read_from(rfilesize, roff), roff, rloc, rsize)
        data = (kip1_blz_decompress(f.read_from(dfilesize, doff)), None, dloc, dsize) if flags & 4 else (f.read_from(dfilesize, doff), doff, dloc, dsize)

        super(KipFile, self).__init__(text, ro, data, bsssize)


class NxoException(Exception):
    pass


def load_nxo(fileobj):
    fileobj.seek(0)
    header = fileobj.read(0x14)

    if header[:4] == b'NSO0':
        return NsoFile(fileobj)
    elif header[0x10:0x14] == b'NRO0':
        return NroFile(fileobj)
    elif header[:4] == b'KIP1':
        return KipFile(fileobj)
    else:
        raise NxoException("not an NRO or NSO or KIP file")


try:
    import idaapi
    import idc
    import ida_funcs
    import ida_loader
    import ida_netnode
except ImportError:
    pass
else:
    # IDA specific code
    def accept_file(li, n):
        print('accept_file')
        if not isinstance(n, int_types) or n == 0:
            li.seek(0)
            if li.read(4) == b'NSO0':
                return 'nxo.py: Switch binary (NSO)'
            li.seek(0)
            if li.read(4) == b'KIP1':
                return 'nxo.py: Switch binary (KIP)'
            li.seek(0x10)
            if li.read(4) == b'NRO0':
                return 'nxo.py: Switch binary (NRO)'
        return 0

    def ida_make_offset(f, ea):
        if f.armv7:
            idaapi.create_data(ea, idc.FF_DWORD, 4, idaapi.BADADDR)
        else:
            idaapi.create_data(ea, idc.FF_QWORD, 8, idaapi.BADADDR)
        idc.op_plain_offset(ea, 0, 0)

    def find_bl_targets(text_start, text_end):
        targets = set()
        for pc in range(text_start, text_end, 4):
            d = idc.get_wide_dword(pc)
            if (d & 0xfc000000) == 0x94000000:
                imm = d & 0x3ffffff
                if imm & 0x2000000:
                    imm |= ~0x1ffffff
                if 0 <= imm <= 2:
                    continue
                target = pc + imm * 4
                if target >= text_start and target < text_end:
                    targets.add(target)
        return targets

    def load_file(li, neflags, format):
        idaapi.set_processor_type("arm", idaapi.SETPROC_LOADER_NON_FATAL|idaapi.SETPROC_LOADER)
        f = load_nxo(li)
        if f.armv7:
            idc.set_inf_attr(idc.INF_LFLAGS, idc.get_inf_attr(idc.INF_LFLAGS) | idc.LFLG_PC_FLAT)
        else:
            idc.set_inf_attr(idc.INF_LFLAGS, idc.get_inf_attr(idc.INF_LFLAGS) | idc.LFLG_64BIT)

        idc.set_inf_attr(idc.INF_DEMNAMES, idaapi.DEMNAM_GCC3)
        idaapi.set_compiler_id(idaapi.COMP_GNU)
        idaapi.add_til('gnulnx_arm' if f.armv7 else 'gnulnx_arm64', 1)

        loadbase = 0x60000000 if f.armv7 else 0x7100000000

        f.binfile.seek(0)
        as_string = f.binfile.read(f.bssoff)
        idaapi.mem2base(as_string, loadbase, -1)
        if f.text[1] != None:
            li.file2base(f.text[1], loadbase + f.text[2], loadbase + f.text[2] + f.text[3], True)
        if f.ro[1] != None:
            li.file2base(f.ro[1], loadbase + f.ro[2], loadbase + f.ro[2] + f.ro[3], True)
        if f.data[1] != None:
            li.file2base(f.data[1], loadbase + f.data[2], loadbase + f.data[2] + f.data[3], True)

        for start, end, name, kind in f.sections:
            if name.startswith('.got'):
                kind = 'CONST'
            idaapi.add_segm(0, loadbase+start, loadbase+end, name, kind)
            segm = idaapi.get_segm_by_name(name)
            if kind == 'CONST':
                segm.perm = idaapi.SEGPERM_READ
            elif kind == 'CODE':
                segm.perm = idaapi.SEGPERM_READ | idaapi.SEGPERM_EXEC
            elif kind == 'DATA':
                segm.perm = idaapi.SEGPERM_READ | idaapi.SEGPERM_WRITE
            elif kind == 'BSS':
                segm.perm = idaapi.SEGPERM_READ | idaapi.SEGPERM_WRITE
            idaapi.update_segm(segm)
            idaapi.set_segm_addressing(segm, 1 if f.armv7 else 2)

        # do imports
        undef_count = 0
        for s in f.symbols:
            if not s.shndx and s.name:
                undef_count += 1
        last_ea = max(loadbase + end for start, end, name, kind in f.sections)
        undef_entry_size = 8
        undef_ea = ((last_ea + 0xFFF) & ~0xFFF) + undef_entry_size # plus 8 so we don't end up on the "end" symbol
        idaapi.add_segm(0, undef_ea, undef_ea+undef_count*undef_entry_size, "UNDEF", "XTRN")
        segm = idaapi.get_segm_by_name("UNDEF")
        segm.type = idaapi.SEG_XTRN
        idaapi.update_segm(segm)
        # Defined dynamic symbols are the module's exports: ELF has no
        # separate export table, the defined (shndx != 0) .dynsym entries
        # ARE it.  Register FUNC and OBJECT symbols as entry points (IDA's
        # "Exports" window), the way PE loaders register their export
        # directory, which lists data exports too; other symbol types and
        # non-export visibilities (STV_INTERNAL/STV_HIDDEN) only get a name.
        objects = aliases = 0
        entry_eas = set()
        for i,s in enumerate(f.symbols):
            if not s.shndx and s.name:
                idaapi.create_data(undef_ea, idc.FF_QWORD, 8, idaapi.BADADDR)
                idaapi.force_name(undef_ea, s.name)
                s.resolved = undef_ea
                undef_ea += undef_entry_size
            elif i != 0:
                if not s.shndx:
                    # unnamed UNDEF slot (never seen in the wild); the old
                    # code asserted here
                    s.resolved = idaapi.BADADDR
                else:
                    s.resolved = loadbase + s.value
                    # SHN_ABS/SHN_COMMON/... (>= 0xff00): st_value is not a
                    # section offset, so resolved is bogus -- don't name it
                    if s.shndx < 0xff00 and s.name:
                        if s.type in (STT_FUNC, STT_OBJECT) and s.vis not in (STV_INTERNAL, STV_HIDDEN):
                            # same-address aliases (C1/C2 folding, ICF): IDA
                            # keeps a single entry per address; aliases just
                            # counts the folded names
                            if s.resolved in entry_eas:
                                aliases += 1
                            entry_eas.add(s.resolved)
                            if s.type == STT_OBJECT:
                                objects += 1
                            idaapi.add_entry(s.resolved, s.resolved, s.name, 0)
                        else:
                            idaapi.force_name(s.resolved, s.name)
            else:
                # NULL symbol
                s.resolved = 0
        if entry_eas:
            print('%d exports (%d objects, %d aliases)' % (len(entry_eas), objects, aliases))

        # Defined STT_FUNC symbols are function candidates; the linker also
        # recorded each one's exact st_size, so keep the size alongside
        # (when it fits inside .text) and let the application loop below
        # create the function with real boundaries instead of leaving them
        # for auto-analysis to guess -- guessed edges are what makes the
        # decompiler misjudge inlining and truncate at junk instructions.
        # Same-address aliases (ICF folding) are identical code, so the
        # first size seen wins.
        funcs = set()
        sized_funcs = {}
        for s in f.symbols:
            if s.name and s.shndx and s.value:
                if s.type == STT_FUNC:
                    ea = loadbase+s.value
                    funcs.add(ea)
                    if s.size and f.textoff <= s.value and s.value + s.size <= f.textoff + f.textsize:
                        sized_funcs.setdefault(ea, s.size)

        # imports: (ea, name) pairs gathered while applying relocations --
        # only undefined dynamic symbols actually referenced by a symbolic
        # relocation are real imports (see the loop below)
        got_name_lookup = {}
        imports = []
        for offset, r_type, sym, addend in f.relocations:
            target = offset + loadbase
            if r_type in (R_ARM_GLOB_DAT, R_ARM_JUMP_SLOT, R_ARM_ABS32):
                if not sym:
                    print('error: relocation at %X failed' % target)
                else:
                    idaapi.put_dword(target, sym.resolved)
                    if not sym.shndx and sym.name:
                        imports.append((target, sym.name))
            elif r_type == R_ARM_RELATIVE:
                idaapi.put_dword(target, idaapi.get_dword(target) + loadbase)
            elif r_type == R_ARM_IRELATIVE:
                # IFUNC, REL flavour (see the R_AARCH64_IRELATIVE branch
                # below for the semantics): the implicit addend already
                # stored in the slot is the resolver's module-relative
                # address, so the write matches R_ARM_RELATIVE above and
                # the pre-rebase slot value is the resolver.
                resolver = idaapi.get_dword(target) + loadbase
                idaapi.put_dword(target, resolver)
                if f.textoff <= resolver - loadbase < f.textoff + f.textsize:
                    funcs.add(resolver)
            elif r_type in (R_AARCH64_GLOB_DAT, R_AARCH64_JUMP_SLOT, R_AARCH64_ABS64):
                if sym is None:
                    # r_sym == 0: no symbol attached, behave like R_AARCH64_RELATIVE
                    idaapi.put_qword(target, loadbase + addend)
                else:
                    idaapi.put_qword(target, sym.resolved + addend)
                    if not sym.shndx and sym.name:
                        imports.append((target, sym.name))
                    if addend == 0:
                        got_name_lookup[offset] = sym.name
            elif r_type == R_AARCH64_RELATIVE:
                idaapi.put_qword(target, loadbase + addend)
                if addend < f.textsize:
                    funcs.add(loadbase + addend)
            elif r_type == R_AARCH64_IRELATIVE:
                # IFUNC: the addend is a *resolver* function rtld CALLS at
                # load time; the slot then receives the resolver's return
                # value, the implementation address it picked for this CPU
                # (memcpy variants and friends).  Statically the resolver
                # cannot be run, so pointing the slot at the resolver
                # itself is the only truthful static value and keeps the
                # offset/xref chain usable.  Registering the resolver as a
                # function matters because nothing else finds it: it is
                # only ever called by rtld through this relocation, so no
                # in-module BL reaches it and it carries no dynsym symbol.
                # r_sym is 0 per the ABI (the addend carries everything).
                idaapi.put_qword(target, loadbase + addend)
                if f.textoff <= addend < f.textoff + f.textsize:
                    funcs.add(loadbase + addend)
            else:
                print('TODO r_type %d' % (r_type,))
            ida_make_offset(f, target)

        # DT_INIT / DT_FINI are plain function addresses recorded in
        # .dynamic itself (not relocation targets): rtld calls them right
        # after mapping the module / right before unloading it.  No other
        # discovery path in this loader finds them -- they are typically
        # only ever called by rtld, so no in-module BL reaches them either.
        # Name them only when no dynsym symbol already did (BotW-era
        # modules export real _init/_fini symbols, firmware modules carry
        # neither the symbols nor any name).
        for tag, name in ((DT_INIT, '_init'), (DT_FINI, '_fini')):
            val = f.dynamic.get(tag, 0)
            if val and f.textoff <= val < f.textoff + f.textsize:
                ea = loadbase + val
                funcs.add(ea)
                if not idc.get_name(ea):
                    idaapi.force_name(ea, name)

        # INIT_ARRAY / FINI_ARRAY are pointer tables in .data listing the
        # remaining init/fini callbacks (C++ ctors/dtors among them).  The
        # apply loop above has already fixed every entry up to its final
        # loadbase+target value (both RELA and RELR paths land there), so
        # read the values back and treat each in-text target as a function
        # candidate.  The relative-addend rule in the apply loop covers
        # most of these already; reading the arrays also catches entries
        # whose relocations use types this loader does not unpack.
        for tag, szkey in ((DT_INIT_ARRAY, DT_INIT_ARRAYSZ), (DT_FINI_ARRAY, DT_FINI_ARRAYSZ)):
            arroff, arrsz = f.dynamic.get(tag), f.dynamic.get(szkey)
            if arroff is None or not arrsz:
                continue
            for i in iter_range(arrsz // f.offsize):
                slot = loadbase + arroff + i*f.offsize
                val = idaapi.get_qword(slot) if not f.armv7 else idaapi.get_dword(slot)
                if loadbase + f.textoff <= val < loadbase + f.textoff + f.textsize:
                    funcs.add(val)

        # Register imported (undefined) symbols so they show up in IDA's
        # "Imports" window, the way native file loaders do (PE/COFF register
        # their IAT slots).  Each entry's ea is the GOT/data slot the
        # relocation patched -- double-clicking it in the window jumps there.
        # ELF records no symbol-to-library mapping: at runtime rtld/ld.so
        # just searches the DT_NEEDED modules in order, so attribute all
        # imports to the first needed module (placeholder name if none).
        # API contract: fill a fresh netnode with set_import_name() entries,
        # then import_module() attaches it under the library name.
        if imports:
            modnode = ida_netnode.netnode()
            modnode.create()
            modidx = modnode.index()
            for ea, name in imports:
                ida_loader.set_import_name(modidx, ea, name)
            modname = f.needed[0] if f.needed else 'unknown'
            # NintendoSDK links write full build-host paths into DT_NEEDED
            # (e.g. BotW: "D:/home/Cafe/U-King/.../nnSdk.nss"); rtld identifies
            # modules by basename, so show that when one is present.
            modname = modname.rsplit('/', 1)[-1].rsplit('\\', 1)[-1] or modname
            ida_loader.import_module(modname, None, modidx, None, None)
            print('%d imports from %s' % (len(imports), modname))

        for func, target in f.plt_entries:
            if target in got_name_lookup:
                addr = loadbase + func
                funcs.add(addr)
                idaapi.force_name(addr, got_name_lookup[target])

        funcs |= find_bl_targets(loadbase, loadbase+f.textsize)

        # Descending order: when an over-recorded st_size would swallow the
        # entry of an already-created function, add_func fails and that
        # address falls back to the old AutoMark path.  add_func also
        # refuses to start on bytes that are not an instruction yet, and
        # during load nothing has been decoded, so create the entry
        # instruction first (without it every add_func call fails and the
        # pinning is a silent no-op).
        for addr in sorted(funcs, reverse=True):
            size = sized_funcs.get(addr)
            if size:
                if not idaapi.is_code(idaapi.get_flags(addr)):
                    idaapi.create_insn(addr)
                if ida_funcs.add_func(addr, addr + size):
                    continue
            idc.AutoMark(addr, idc.AU_CODE)
            idc.AutoMark(addr, idc.AU_PROC)

        # Record module identity where the user will find it: the Output
        # window during load, a comment on the module's first byte and one
        # on its first segment.  For the module id (Build ID): community
        # symbol tables and cheat/mod files key on this value (yuzu matches
        # mods by the full 64-hex id, cheats by its first 16 chars); the
        # SONAME is the rtld-visible module name DT_NEEDED entries resolve
        # against; the NEEDED line lists the DT_NEEDED dependencies; the SDK
        # line names the nnSdk the module was built against (ModuleVersion
        # triplet behind the rocrt +8 pointer on 17.x, the .api_info
        # component strings on older SDKs); for KIPs the header
        # identity/scheduling summary joins the SONAME (17.0.1 KIPs do carry
        # one, e.g. "fs.nss"; they have no Build ID field and no DT_NEEDED
        # -- fully self-contained modules).  The Segments line summarizes
        # the four-segment memory footprint, including the .bss range which
        # has no backing in the file.
        # A *repeatable* comment at loadbase does not survive
        # initial auto-analysis (measured on IDA 9.4); the regular comment
        # and the segment comment do -- and both are wholesale replacements,
        # so every identity line is collected and written once.
        idlines = []
        # an all-zero Build ID means absent (early libnx NROs like
        # ChoiDujourNX v1.0.1 leave it zeroed) -- print nothing rather
        # than 64 zeros
        if f.module_id and any(f.module_id):
            build_id = ''.join('%02x' % c for c in bytes_to_list(f.module_id))
            print('Build ID: %s' % build_id)
            idlines.append('Build ID: %s' % build_id)
        if f.soname:
            print('SONAME: %s' % f.soname)
            idlines.append('SONAME: %s' % f.soname)
        if f.needed:
            # rtld matches DT_NEEDED entries by basename (see the import
            # registration above), so summarize by basename -- the full
            # NintendoSDK build paths some games write here stay visible
            # in .dynstr.
            names = [n.rsplit('/', 1)[-1].rsplit('\\', 1)[-1] or n for n in f.needed]
            print('NEEDED: %s' % ', '.join(names))
            idlines.append('NEEDED: %s' % ', '.join(names))
        sdkline = None
        if f.sdk_version:
            sdkline = 'SDK: nnSdk %d.%d.%d' % f.sdk_version
        elif f.api_components:
            # older SDKs list every linked component, middleware included:
            # "SDK MW+Nintendo+NintendoWare_G3d-4_4_0-Release",
            # "SDK MW+Microsoft+Havok-2014_2", "SDK MW+Nintendo+NEX-4_2_1-ALZ".
            # The NintendoSDK version is the first Nintendo -Release entry.
            for c in f.api_components:
                m = re.match(r'SDK MW\+Nintendo\+\S+-(\d+)_(\d+)_(\d+)-Release$', c)
                if m:
                    sdkline = 'SDK: NintendoSDK %s.%s.%s (%d component%s)' % (
                        m.group(1), m.group(2), m.group(3),
                        len(f.api_components), '' if len(f.api_components) == 1 else 's')
                    break
        if sdkline:
            print(sdkline)
            idlines.append(sdkline)
        if f.kip_name:
            kipline = 'KIP: %s (program id %016x, version %d, priority %d, core %d, stack 0x%x)' % (
                f.kip_name, f.kip_program_id, f.kip_version, f.kip_priority,
                f.kip_core, f.kip_stack_size)
            print(kipline)
            idlines.append(kipline)
        segparts = []
        for name, start, size in (
            ('.text', f.textoff, f.textsize),
            ('.rodata', f.rodataoff, f.rodatasize),
            ('.data', f.dataoff, f.datasize),
            ('.bss', f.bssoff, f.bsssize),
        ):
            if size:
                segparts.append('%s 0x%x-0x%x' % (name, start, start + size))
        if segparts:
            # module-relative ranges; IDA's Segments window shows the
            # flattened sub-sections, this is the four-container overview
            print('Segments: %s' % ' | '.join(segparts))
            idlines.append('Segments: %s' % ' | '.join(segparts))
        if idlines:
            cmt = '\n'.join(idlines)
            idc.set_cmt(loadbase, cmt, 0)
            idaapi.set_segment_cmt(idaapi.getseg(loadbase), cmt, 1)

        return 1
