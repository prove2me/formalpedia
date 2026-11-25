-- Prove2me | Theorems.Thm_Poly1305Debian_internalOk_poly1305_blocks_v2
-- name    : Poly1305Debian.internalOk_poly1305_blocks_v2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-25T21:18:29.429028+00:00
-- url     : https://prove2.me/theorems/3ec2c479-47b6-52a1-8390-e76b19018984
-- title:
--   poly1305_donna64.h, poly1305_blocks — the block loop runs h ← r·(h + block + hibit) mod 2^130 − 5
-- statement:
--   Total correctness of the internal function `poly1305_blocks` in Debian's AArch64 object code of libsodium's `poly1305_donna.c` (in `libsodiumDebianOnetimeauthLib`), under the contract `blocksWholeSpec` (bundle `Poly1305Debian_BlocksWhole`: `blocksSpec` with the message length a multiple of 16), for every placement of the library the linker could produce that treats every GOT access to `__stack_chk_guard` alike (`GuardUniform`), and every hook table laid out as a real link lays it out (`Link.PlacedLib.LinkOk`) whose hooks for `sodium_memzero` and `memset` meet `Libc.explicitBzeroSpec` and `VerifiedLibraries.Musl.cryptoMemsetSpec` (`internalOk`, bundle `Poly1305Debian_Spec`); the function calls no hook. The function is a symbol of the code block, though not exported. For every ghost value $(ro, rh, fin, m)$, every frame $R$ and every entry state at the function with the stack pointer 16-byte aligned whose memory satisfies the precondition separately from $R$, execution terminates and returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding; it never panics, exits or runs out of memory.
--   - **Before:** `x0` points to the 48 owned bytes $rh$ of the state's fields `r` and `h` with `StateOk` $rh$, and to the owned `final` byte $fin$ at offset 88; the bytes $m$ are at `x1`, owned or read-only as $ro$ says; `x2` $= |m|$, a multiple of 16 and at least 16; no stack is used.
--   - **After:** `x0` and `x18` are unchanged, and `x0` points to 48 bytes $rh'$ with `StateOk` $rh'$ and the same first 24 bytes (the limbs $r_0, r_1, r_2$), whose accumulator satisfies `limbVal (hLimb rh')` $\equiv$ `blocksAcc (limbVal (rLimb rh)) (hibit fin) (limbVal (hLimb rh)) m` $\pmod{2^{130} - 5}$. That is, $h \leftarrow r \cdot (h + n + b) \bmod (2^{130} - 5)$ for each complete 16-byte block of $m$ in order $n$ its little-endian value and $b = 2^{128}$ if $fin = 0$, $b = 0$ otherwise. $fin$ and $m$ are handed back.
--
--   `poly1305_donna64.h`, lines 65–66, 87, 95 and 112: “const unsigned long long hibit = (st->final) ? 0ULL : (1ULL << 40); /* 1 << 128 */”, “/* h += m[i] */”, “/* h *= r */”, “/* (partial) h %= p */”.
--
--   **Replaces** `Poly1305Debian.internalOk_poly1305_blocks`, which is Disproved (submission 88a8159d): it allowed any length $|m| \ge 16$, and Debian's compiled loop runs until its pointer equals $m + |m|$, so for a length that is not a multiple of 16 it reads past the message. This statement adds the condition that $|m|$ is a multiple of 16.
-- source:
--   libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda), src/libsodium/crypto_onetimeauth/poly1305/donna/poly1305_donna64.h lines 61–133 (poly1305_blocks)

import Definitions.Def_Poly1305Debian_BlocksWhole

namespace Poly1305Debian

theorem internalOk_poly1305_blocks_v2 :
    internalOk "poly1305_blocks [libsodium_la_poly1305_donna]" (fun _ => blocksWholeSpec) := by
  sorry

end Poly1305Debian
