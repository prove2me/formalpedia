-- Prove2me | Theorems.Thm_Poly1305DebianCt_ctPublicOk_crypto_onetimeauth_verify
-- name    : Poly1305DebianCt.ctPublicOk_crypto_onetimeauth_verify
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-26T10:23:42.323646+00:00
-- url     : https://prove2.me/theorems/18cb18a9-1d1d-59b7-a584-d239487d6d1e
-- title:
--   advanced/poly1305.md, crypto_onetimeauth_verify — verifies in constant time (Debian's libsodium, AArch64)
-- statement:
--   libsodium's documentation, `advanced/poly1305.md`, line 72: “The `crypto_onetimeauth_verify()` function verifies, in constant time, that `h` is a correct authenticator for the message `in` whose length is `inlen` bytes, using the secret key `k`.” The term is defined in `helpers/README.md`, line 9: “it means the time needed to perform the comparison is the same for all data of the same size.”
--
--   The export `crypto_onetimeauth_verify` of Debian's AArch64 object code of libsodium 1.0.22 (the objects of `crypto_onetimeauth.c`, `onetimeauth_poly1305.c`, `poly1305_donna.c` and `verify.c` from Debian's `libsodium.a`, unmodified, linked into one library, `libsodiumDebianOnetimeauthCtLib`) is constant-time in the leakage model `Leakage.ct_subroutine_ok`: `ctPublicOk "crypto_onetimeauth_verify" verifyPre verifyPub` (bundle `Poly1305DebianCt_Spec`). This holds under every placement of the library the linker could produce that treats every GOT access to `__stack_chk_guard` alike (`GuardUniform`), and every hook table laid out as a real link lays it out (`Link.PlacedLib.LinkOk`) whose hooks for `sodium_memzero` and `memset` meet `Libc.explicitBzeroSpec` and `VerifiedLibraries.Musl.cryptoMemsetSpec`; a call of `sodium_memzero`, `memset`, `randombytes_buf` or `__stack_chk_fail` reveals its first 2, 3, 2 or 0 argument registers.
--
--   In detail: take two entry states at the function's address that follow the calling convention, have the code loaded and hold the same values in every register, so with the same `h`, `in`, `inlen`, `k` in `x0`–`x3`. Suppose the memory of each holds, separately from an arbitrary frame of its own, the library's data objects in their initial state and `verifyPre` for its own ghost value $(roH, roM, roK, ga, h, m, key, g)$: 16 bytes $h$ at `h`, the message bytes $m$ at `in` with `inlen` $= |m|$ and 32 bytes $key$ at `k` (each owned or read-only, by $roH$, $roM$, $roK$), the stack-protector guard with value $g$ where the code reads it (through a GOT slot holding the address $ga$ unless the linker relaxed the accesses), and the 4352 bytes below the stack pointer. Suppose the two ghost values agree on $roH$, $roM$, $roK$ and $ga$. Then the two runs, up to their return, reveal the same sequence of observations (each step's instruction address, the addresses of its memory accesses and the operands of any division, and a hooked call's arguments) and stop together. Nothing is required of the tag, message, key or guard bytes, which may all differ between the runs: in particular a correct and an incorrect tag cannot be told apart this way.
-- source:
--   libsodium documentation, Secret-key single-message authentication using Poly1305 (https://doc.libsodium.org/advanced/poly1305; source jedisct1/libsodium-doc, commit 5adaf345, https://github.com/jedisct1/libsodium-doc/blob/5adaf34515b79d0b37bd8edbe042f20f3bdba2c6/advanced/poly1305.md), lines 68–72 ("The crypto_onetimeauth_verify() function verifies, in constant time, ..."), with the meaning of "constant time" from libsodium documentation, Helpers (https://doc.libsodium.org/helpers; source jedisct1/libsodium-doc, commit 5adaf345, https://github.com/jedisct1/libsodium-doc/blob/5adaf34515b79d0b37bd8edbe042f20f3bdba2c6/helpers/README.md) line 9; crypto_onetimeauth.c lines 30–35; implemented by the objects of Debian libsodium 1.0.22-2 (arm64), libsodium-dev_1.0.22-2_arm64.deb (https://deb.debian.org/debian/pool/main/libs/libsodium/libsodium-dev_1.0.22-2_arm64.deb), libsodium.a (crypto_onetimeauth.c, onetimeauth_poly1305.c, poly1305_donna.c lines 102–113, verify.c of libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda))

import Definitions.Def_Poly1305DebianCt_Spec

namespace Poly1305DebianCt

theorem ctPublicOk_crypto_onetimeauth_verify :
    ctPublicOk "crypto_onetimeauth_verify" verifyPre verifyPub := by
  sorry

end Poly1305DebianCt
