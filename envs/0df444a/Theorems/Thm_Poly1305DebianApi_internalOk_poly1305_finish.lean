-- Prove2me | Theorems.Thm_Poly1305DebianApi_internalOk_poly1305_finish
-- name    : Poly1305DebianApi.internalOk_poly1305_finish
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-26T11:24:23.527883+00:00
-- url     : https://prove2.me/theorems/52674d4c-467d-500e-8575-6bcca71907ad
-- title:
--   poly1305_donna64.h, poly1305_finish — processes the remaining block, writes (h mod 2^130 − 5) + pad and zeroes the state
-- statement:
--   Total correctness of the internal function `poly1305_finish` in Debian's AArch64 object code of libsodium's `poly1305_donna.c` (in `libsodiumDebianOnetimeauthCtLib`), under the contract `finishSpec`, for every placement of the library the linker could produce that treats every GOT access to `__stack_chk_guard` alike (`GuardUniform`), and every hook table laid out as a real link lays it out (`Link.PlacedLib.LinkOk`) whose hooks for `sodium_memzero` and `memset` meet `Libc.explicitBzeroSpec` and `VerifiedLibraries.Musl.cryptoMemsetSpec` (`internalOk`, bundle `Poly1305DebianApi_Spec`). The function is a symbol of the code block, though not exported. For every ghost value $(st, mac)$, every frame $R$ and every entry state at the function with the stack pointer 16-byte aligned whose memory satisfies the precondition separately from $R$, execution terminates and returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding; it never panics, exits or runs out of memory.
--   - **Before:** `x0` points to the 96 owned state bytes $st$, whose first 48 (`r` and `h`) satisfy `StateOk` and whose `leftover` (offset 64) is below 16; `x1` points to 16 owned bytes; the caller lends the 4128 bytes below the stack pointer.
--   - **After:** the 96 state bytes are zero, `mac` holds `finishTag st`, and the stack frame is handed back. `finishTag st` is computed from $a$, the value of the `h` limbs: if $L$ = `leftover` is not 0, first $a \leftarrow r \cdot (a + n) \bmod (2^{130} - 5)$, with $r$ the value of the `r` limbs and $n$ the little-endian value of the first $L$ bytes of `buffer` followed by the byte `0x01`; then the 16 little-endian bytes of $(a \bmod (2^{130} - 5)) + s$, with $s$ the 128-bit little-endian value of `pad`.
--
--   `poly1305_donna64.h`, lines 143, 156, 180, 189, 199, 212 and 219: “/* process the remaining block */”, “/* fully carry h */”, “/* compute h + -p */”, “/* select h if h < p, or h + -p if h >= p */”, “/* h = (h + pad) */”, “/* mac = h % (2^128) */”, “/* zero out the state */”.
--
--   **Replaces** [`Poly1305Debian.internalOk_poly1305_finish`](https://prove2.me/theorems/18e354a4-b034-4434-a7f1-2f855fecd54c), the same contract for the library `libsodiumDebianOnetimeauthLib` of the first three objects alone; `libsodiumDebianOnetimeauthCtLib` adds `verify.o` after them, so that all of libsodium's Poly1305 API, verification included, is stated over one library.
-- source:
--   libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda), src/libsodium/crypto_onetimeauth/poly1305/donna/poly1305_donna64.h lines 135–221 (poly1305_finish)

import Definitions.Def_Poly1305DebianApi_Spec

namespace Poly1305DebianApi

theorem internalOk_poly1305_finish :
    internalOk "poly1305_finish [libsodium_la_poly1305_donna]" (fun _ => finishSpec) := by
  sorry

end Poly1305DebianApi
