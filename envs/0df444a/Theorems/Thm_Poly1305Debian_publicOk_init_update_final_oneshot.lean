-- Prove2me | Theorems.Thm_Poly1305Debian_publicOk_init_update_final_oneshot
-- name    : Poly1305Debian.publicOk_init_update_final_oneshot
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-25T19:38:29.807674+00:00
-- url     : https://prove2.me/theorems/f1cc6ce5-c1d4-51cb-923f-9a73e146c0cf
-- title:
--   Debian's libsodium crypto_onetimeauth and crypto_onetimeauth_init/update/final compute RFC 8439's Poly1305 tag (AArch64)
-- statement:
--   Two claims about the documented public functions `crypto_onetimeauth`, `crypto_onetimeauth_init`, `crypto_onetimeauth_update` and `crypto_onetimeauth_final`, in Debian's AArch64 object code of libsodium 1.0.22 (the objects of `crypto_onetimeauth.c`, `onetimeauth_poly1305.c` and `poly1305_donna.c` from Debian's `libsodium.a`, unmodified, linked into one library, `libsodiumDebianOnetimeauthLib`, whose exports these four are). Each claim is total correctness under every placement of the library the linker could produce that treats every GOT access to `__stack_chk_guard` alike (`GuardUniform`), and every hook table laid out as a real link lays it out (`Link.PlacedLib.LinkOk`: in particular, two external symbols at one address have the same hook) whose hooks for `sodium_memzero` and `memset` meet `Libc.explicitBzeroSpec` and `VerifiedLibraries.Musl.cryptoMemsetSpec` (`publicOk`, bundle `Poly1305Debian_Spec`). In detail, take every entry state at the function with the stack pointer 16-byte aligned, the library's data objects in their initial state (the pointer `implementation`, the function-pointer table and a string, `PlacedLib.dataInit`), and every frame $R$ held separately. Execution terminates and returns to the caller (the link register) with the stack pointer and the callee-saved registers restored, $R$ untouched, the data objects unchanged, `0` in `w0` and the postcondition holding; it never panics, exits or runs out of memory. Inputs may be owned or read-only memory, and the state, key, input, tag, data objects and stack frame are pairwise disjoint (separating conjunction).
--
--   First, there is a representation predicate $\mathrm{Rep}$ such that the three streaming functions meet `initSpec Rep`, `updateSpec Rep` and `finalSpec Rep`. Here $\mathrm{Rep}(a, st, key, m)$ relates the address $a$ of a 256-byte `crypto_onetimeauth_state`, its bytes $st$, a key and a message:
--   - **`crypto_onetimeauth_init`** (`x0 = state`, `x1 = key`): with 256 owned bytes at `state` and the 32 key bytes $key$ at `key`, it leaves 256 bytes $st'$ at `state` with $\mathrm{Rep}(\mathtt{state}, st', key, [\,])$, and the key unchanged. It uses no stack.
--   - **`crypto_onetimeauth_update`** (`x0 = state`, `x1 = in`, `x2 = inlen`): with 256 owned bytes $st$ at `state` such that $\mathrm{Rep}(\mathtt{state}, st, key, m)$, the bytes $inp$ at `in` and `inlen` $= |inp|$, it leaves 256 bytes $st'$ with $\mathrm{Rep}(\mathtt{state}, st', key, m \mathbin{+\!\!+} inp)$, and $inp$ unchanged. It uses the 48 bytes below the stack pointer.
--   - **`crypto_onetimeauth_final`** (`x0 = state`, `x1 = out`): with 256 owned bytes $st$ at `state` such that $\mathrm{Rep}(\mathtt{state}, st, key, m)$ and 16 owned bytes at `out`, it writes `poly1305Mac m key` (RFC 8439 §2.5.1) to `out`, sets the first 96 bytes of the state to zero and leaves the other 160 unchanged. It uses the 4144 bytes below the stack pointer.
--
--   Second, **`crypto_onetimeauth(out, in, inlen, k)`** meets `oneshotSpec`: with 16 owned bytes at `out`, the bytes $m$ at `in`, `inlen` $= |m|$ and the 32 key bytes $key$ at `k`, with the stack-protector guard readable where the code reads it (`guardRes`), it writes `poly1305Mac m key` to `out` and leaves $m$, $key$ and the guard unchanged. It uses the 4320 bytes below the stack pointer.
--
--   Chaining the streaming contracts: a caller that runs `crypto_onetimeauth_init(state, key)`, then any number $k \ge 0$ of calls `crypto_onetimeauth_update(state, in_j, inlen_j)`, then `crypto_onetimeauth_final(state, out)`, all on the same `state`, and does not touch `state` or `out` in between, finds in `out` the `poly1305Mac` of the concatenated inputs under the key, the tag the one-shot computes. This follows by induction over the calls from the three contracts and the frame rule; it is not a separate statement.
--
--   libsodium documentation, *Secret-key single-message authentication using Poly1305*, lines 65, 94, 98 and 100: “The `crypto_onetimeauth()` function authenticates a message `in` whose length is `inlen` using a secret key `k` (`crypto_onetimeauth_KEYBYTES` bytes) and puts the authenticator into `out` (`crypto_onetimeauth_BYTES` bytes).” “The `crypto_onetimeauth_init()` function initializes a structure pointed by `state` using a key `key`.” “`crypto_onetimeauth_update()` can then be called more than once in order to compute the authenticator from sequential chunks of the message.” “Finally, `crypto_onetimeauth_final()` puts the authenticator into `out`.”
-- source:
--   libsodium documentation, Secret-key single-message authentication using Poly1305 (https://doc.libsodium.org/advanced/poly1305; source jedisct1/libsodium-doc, commit 5adaf345, https://github.com/jedisct1/libsodium-doc/blob/5adaf34515b79d0b37bd8edbe042f20f3bdba2c6/advanced/poly1305.md), lines 65 and 94–104 (crypto_onetimeauth, crypto_onetimeauth_init, _update, _final), implemented by the objects of Debian libsodium 1.0.22-2 (arm64), libsodium-dev_1.0.22-2_arm64.deb (https://deb.debian.org/debian/pool/main/libs/libsodium/libsodium-dev_1.0.22-2_arm64.deb), libsodium.a (crypto_onetimeauth.c, onetimeauth_poly1305.c, poly1305_donna.c of libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda))

import Definitions.Def_Poly1305Debian_Spec

namespace Poly1305Debian

theorem publicOk_init_update_final_oneshot :
    (∃ Rep : Poly1305Libsodium.StateRep, initPublicOk Rep ∧ updatePublicOk Rep ∧ finalPublicOk Rep) ∧
      oneshotPublicOk := by
  sorry

end Poly1305Debian
