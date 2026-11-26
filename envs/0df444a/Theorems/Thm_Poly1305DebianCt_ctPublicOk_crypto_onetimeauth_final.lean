-- Prove2me | Theorems.Thm_Poly1305DebianCt_ctPublicOk_crypto_onetimeauth_final
-- name    : Poly1305DebianCt.ctPublicOk_crypto_onetimeauth_final
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-26T10:23:20.431821+00:00
-- url     : https://prove2.me/theorems/1d6fffca-18bc-5bf1-b0f3-98f082894d33
-- title:
--   advanced/poly1305.md, crypto_onetimeauth_final — constant time for a given buffered count (Debian's libsodium, AArch64)
-- statement:
--   The export `crypto_onetimeauth_final` of `libsodiumDebianOnetimeauthCtLib` (Debian's AArch64 objects of libsodium 1.0.22, unmodified) is constant-time in the leakage model `Leakage.ct_subroutine_ok`: `ctPublicOk "crypto_onetimeauth_final" finalPre leftoverPub` (bundle `Poly1305DebianCt_Spec`), under every placement and hook table the judgment admits (`Placeable`, `GuardUniform`, `Link.PlacedLib.LinkOk`, and hooks for `sodium_memzero` and `memset` meeting `Libc.explicitBzeroSpec` and `VerifiedLibraries.Musl.cryptoMemsetSpec`; a call of `memset` reveals `x0`–`x2`, one of `sodium_memzero` `x0`–`x1`).
--
--   In detail: take two entry states at the function's address that follow the calling convention, have the code loaded and hold the same values in every register, so with the same `state` and `out` in `x0` and `x1`. Suppose the memory of each holds, separately from an arbitrary frame of its own, the library's data objects in their initial state and `finalPre` for its own ghost value $(st, mac)$: 256 owned state bytes $st$ at `state` whose `leftover` word (offset 64) is below 16, 16 owned bytes at `out`, and the 4144 bytes below the stack pointer. Suppose the two `leftover` words are equal. Then the two runs reveal the same sequence of observations up to their return and stop together, whatever the other state bytes and the output bytes are. No invariant on the state is assumed.
-- source:
--   libsodium documentation, Secret-key single-message authentication using Poly1305 (https://doc.libsodium.org/advanced/poly1305; source jedisct1/libsodium-doc, commit 5adaf345, https://github.com/jedisct1/libsodium-doc/blob/5adaf34515b79d0b37bd8edbe042f20f3bdba2c6/advanced/poly1305.md), lines 90–92 and 100–104 (crypto_onetimeauth_final), implemented by crypto_onetimeauth.c lines 54–60 and poly1305_donna.c lines 93–100 of libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda)

import Definitions.Def_Poly1305DebianCt_Spec

namespace Poly1305DebianCt

theorem ctPublicOk_crypto_onetimeauth_final :
    ctPublicOk "crypto_onetimeauth_final" finalPre leftoverPub := by
  sorry

end Poly1305DebianCt
