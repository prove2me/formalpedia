-- Prove2me | Theorems.Thm_Poly1305Libsodium_internalOk_poly1305_blocks
-- name    : Poly1305Libsodium.internalOk_poly1305_blocks
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-24T21:07:06.327673+00:00
-- url     : https://prove2.me/theorems/cda5fddc-d57c-42a8-8434-cc22e0e2d25f
-- title:
--   poly1305_donna64.h, poly1305_blocks — the block loop runs h ← r·(h + block + hibit) mod 2^130 − 5
-- statement:
--   Total correctness of the internal function `poly1305_blocks` in the AArch64 object code of libsodium's `poly1305_donna.c` (`libsodiumPoly1305Lib`), under the contract `blocksSpec`, for every placement of the library the linker could produce and every hook for `sodium_memzero` meeting `Libc.explicitBzeroSpec` (the function calls no hook). The function is a symbol of the code block, though not exported. For every ghost value $(ro, rh, fin, m)$, every frame $R$ and every entry state at the function with the stack pointer 16-byte aligned whose memory satisfies the precondition separately from $R$, execution terminates and returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding; it never panics, exits or runs out of memory.
--   - **Before:** `x0` points to the 48 owned bytes $rh$ of the state's fields `r` and `h` with `StateOk` $rh$, and to the owned `final` byte $fin$ at offset 88; the bytes $m$ are at `x1`, owned or read-only as $ro$ says; `x2` $= |m| \ge 16$; the caller lends the 64 bytes below the stack pointer.
--   - **After:** `x0` points to 48 bytes $rh'$ with `StateOk` $rh'$ and the same first 24 bytes (the limbs $r_0, r_1, r_2$), whose accumulator satisfies `limbVal (hLimb rh')` $\equiv$ `blocksAcc (limbVal (rLimb rh)) (hibit fin) (limbVal (hLimb rh)) m` $\pmod{2^{130} - 5}$. That is, $h \leftarrow r \cdot (h + n + b) \bmod (2^{130} - 5)$ for each complete 16-byte block of $m$ in order (the last $|m| \bmod 16$ bytes are ignored), $n$ its little-endian value and $b = 2^{128}$ if $fin = 0$, $b = 0$ otherwise. $fin$, $m$ and the stack frame are handed back.
--
--   `poly1305_donna64.h`, lines 65–66, 87, 95 and 112: “const unsigned long long hibit = (st->final) ? 0ULL : (1ULL << 40); /* 1 << 128 */”, “/* h += m[i] */”, “/* h *= r */”, “/* (partial) h %= p */”.
-- source:
--   libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda), src/libsodium/crypto_onetimeauth/poly1305/donna/poly1305_donna64.h lines 61–133 (poly1305_blocks)

import Definitions.Def_Poly1305Libsodium_Spec

namespace Poly1305Libsodium

theorem internalOk_poly1305_blocks :
    internalOk "poly1305_blocks [libsodium_poly1305_donna]" (fun _ => blocksSpec) := by
  sorry

end Poly1305Libsodium
