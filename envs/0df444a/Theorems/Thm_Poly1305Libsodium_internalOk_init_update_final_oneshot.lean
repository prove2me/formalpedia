-- Prove2me | Theorems.Thm_Poly1305Libsodium_internalOk_init_update_final_oneshot
-- name    : Poly1305Libsodium.internalOk_init_update_final_oneshot
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-24T21:25:10.120801+00:00
-- url     : https://prove2.me/theorems/819a9a22-c313-420d-81e0-ec967c8b2d02
-- title:
--   crypto_onetimeauth_poly1305 (donna64) — the one-shot and init/update/final compute RFC 8439's Poly1305 tag
-- statement:
--   Two claims about the AArch64 object code of libsodium's `poly1305_donna.c` (`libsodiumPoly1305Lib`), each with total correctness under every placement of the library the linker could produce and every hook for `sodium_memzero` meeting `Libc.explicitBzeroSpec`. In detail, for every entry state at the function with the stack pointer 16-byte aligned and every frame $R$ held separately, execution terminates and returns to the caller (the link register) with the stack pointer and the callee-saved registers restored, $R$ untouched, `0` in `w0` and the postcondition holding; it never panics, exits or runs out of memory. Inputs may be owned or read-only memory, and the state, key, input, tag and stack frame are pairwise disjoint (separating conjunction).
--
--   First, there is a representation predicate $\mathrm{Rep}$ such that the three streaming functions meet `initSpec Rep`, `updateSpec Rep` and `finalSpec Rep`. Here $\mathrm{Rep}(a, st, key, m)$ relates the address $a$ of a 256-byte `crypto_onetimeauth_poly1305_state`, its bytes $st$, a key and a message:
--   - **init** (`x0 = state`, `x1 = key`): with 256 owned bytes at `state` and the 32 key bytes $key$ at `key`, it leaves 256 bytes $st'$ at `state` with $\mathrm{Rep}(\mathtt{state}, st', key, [\,])$, and the key unchanged.
--   - **update** (`x0 = state`, `x1 = in`, `x2 = inlen`): with 256 owned bytes $st$ at `state` such that $\mathrm{Rep}(\mathtt{state}, st, key, m)$, the bytes $inp$ at `in` and `inlen` $= |inp|$, it leaves 256 bytes $st'$ with $\mathrm{Rep}(\mathtt{state}, st', key, m \mathbin{+\!\!+} inp)$, and $inp$ unchanged. It uses the 112 bytes below the stack pointer.
--   - **final** (`x0 = state`, `x1 = out`): with 256 owned bytes $st$ at `state` such that $\mathrm{Rep}(\mathtt{state}, st, key, m)$ and 16 owned bytes at `out`, it writes `poly1305Mac m key` (RFC 8439 §2.5.1) to `out`, sets the first 96 bytes of the state to zero and leaves the other 160 unchanged. It uses the 4112 bytes below the stack pointer.
--
--   Second, the one-shot `crypto_onetimeauth_poly1305_donna(out, m, inlen, key)` meets `oneshotSpec`: with 16 owned bytes at `out`, the bytes $m$ at `m`, `inlen` $= |m|$ and the 32 key bytes $key$ at `key`, it writes `poly1305Mac m key` to `out` and leaves $m$ and $key$ unchanged. It uses the 4336 bytes below the stack pointer.
--
--   Chaining the streaming contracts: after `_init(state, key)`, any number $k \ge 0$ of calls `_update(state, in_j, inlen_j)` and `_final(state, out)`, all on the same `state`, `out` holds `poly1305Mac` of the concatenation of the inputs, with the key, as the one-shot computes it.
--
--   libsodium documentation, *Secret-key single-message authentication using Poly1305*, lines 65, 94, 98 and 100: “The `crypto_onetimeauth()` function authenticates a message `in` whose length is `inlen` using a secret key `k` (`crypto_onetimeauth_KEYBYTES` bytes) and puts the authenticator into `out` (`crypto_onetimeauth_BYTES` bytes).” “The `crypto_onetimeauth_init()` function initializes a structure pointed by `state` using a key `key`.” “`crypto_onetimeauth_update()` can then be called more than once in order to compute the authenticator from sequential chunks of the message.” “Finally, `crypto_onetimeauth_final()` puts the authenticator into `out`.”
-- source:
--   libsodium documentation, Secret-key single-message authentication using Poly1305 (https://doc.libsodium.org/advanced/poly1305; source jedisct1/libsodium-doc, commit 5adaf345, https://github.com/jedisct1/libsodium-doc/blob/5adaf34515b79d0b37bd8edbe042f20f3bdba2c6/advanced/poly1305.md), lines 65 and 94–104 (crypto_onetimeauth, crypto_onetimeauth_init, _update, _final), implemented by src/libsodium/crypto_onetimeauth/poly1305/donna/poly1305_donna.c lines 58–100 of libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda)

import Definitions.Def_Poly1305Libsodium_Spec

namespace Poly1305Libsodium

theorem internalOk_init_update_final_oneshot :
    (∃ Rep : StateRep, initOk Rep ∧ updateOk Rep ∧ finalOk Rep) ∧ oneshotOk := by
  sorry

end Poly1305Libsodium
