-- Prove2me | Theorems.Thm_Poly1305DebianCt_ctPublicOk_crypto_onetimeauth_init
-- name    : Poly1305DebianCt.ctPublicOk_crypto_onetimeauth_init
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-26T10:22:15.082742+00:00
-- url     : https://prove2.me/theorems/f65fdee6-d510-5602-a71d-b659cf50bb01
-- title:
--   advanced/poly1305.md, crypto_onetimeauth_init — constant time in the key (Debian's libsodium, AArch64)
-- statement:
--   The export `crypto_onetimeauth_init` of `libsodiumDebianOnetimeauthCtLib` (Debian's AArch64 objects of libsodium 1.0.22, unmodified) is constant-time in the leakage model `Leakage.ct_subroutine_ok`: `ctPublicOk "crypto_onetimeauth_init" initPre initPub` (bundle `Poly1305DebianCt_Spec`), under every placement and hook table the judgment admits (`Placeable`, `GuardUniform`, `Link.PlacedLib.LinkOk`, and hooks for `sodium_memzero` and `memset` meeting `Libc.explicitBzeroSpec` and `VerifiedLibraries.Musl.cryptoMemsetSpec`).
--
--   In detail: take two entry states at the function's address that follow the calling convention, have the code loaded and hold the same values in every register, so with the same `state` and `key` in `x0` and `x1`. Suppose the memory of each holds, separately from an arbitrary frame of its own, the library's data objects in their initial state and `initPre` for its own ghost value $(ro, st, key)$: 256 owned bytes $st$ at `state` and 32 bytes $key$ at `key` (owned or read-only, by $ro$). Suppose the two ghost values agree on $ro$. Then the two runs reveal the same sequence of observations up to their return and stop together, whatever the key and the old state bytes are. No stack is used.
-- source:
--   libsodium documentation, Secret-key single-message authentication using Poly1305 (https://doc.libsodium.org/advanced/poly1305; source jedisct1/libsodium-doc, commit 5adaf345, https://github.com/jedisct1/libsodium-doc/blob/5adaf34515b79d0b37bd8edbe042f20f3bdba2c6/advanced/poly1305.md), lines 79–82 and 94 (crypto_onetimeauth_init), implemented by crypto_onetimeauth.c lines 37–43 and poly1305_donna.c lines 72–81 of libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda)

import Definitions.Def_Poly1305DebianCt_Spec

namespace Poly1305DebianCt

theorem ctPublicOk_crypto_onetimeauth_init :
    ctPublicOk "crypto_onetimeauth_init" initPre initPub := by
  sorry

end Poly1305DebianCt
