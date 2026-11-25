-- Prove2me | Theorems.Thm_Poly1305Debian_internalOk_donna_init_update_final_oneshot
-- name    : Poly1305Debian.internalOk_donna_init_update_final_oneshot
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-25T17:05:04.673981+00:00
-- url     : https://prove2.me/theorems/7c90aa67-98bc-4fa8-ab97-4d95b700c086
-- title:
--   poly1305_donna.c — the donna one-shot and init/update/final compute RFC 8439's Poly1305 tag
-- statement:
--   Two claims about the four `static` functions of Debian's AArch64 object code of libsodium's `poly1305_donna.c` that the public API reaches (in `libsodiumDebianOnetimeauthLib`), each with total correctness under every placement of the library the linker could produce that treats every GOT access to `__stack_chk_guard` alike (`GuardUniform`), and every hook table laid out as a real link lays it out (`Link.PlacedLib.LinkOk`: in particular, two external symbols at one address have the same hook) whose hooks for `sodium_memzero` and `memset` meet `Libc.explicitBzeroSpec` and `VerifiedLibraries.Musl.cryptoMemsetSpec` (`internalOk`, bundle `Poly1305Debian_Spec`). In detail, take every entry state at the function with the stack pointer 16-byte aligned and every frame $R$ held separately. Execution terminates and returns to the caller (the link register) with the stack pointer and the callee-saved registers restored, $R$ untouched, `0` in `w0` and the postcondition holding; it never panics, exits or runs out of memory. Inputs may be owned or read-only memory, and the state, key, input, tag and stack frame are pairwise disjoint (separating conjunction).
--
--   First, there is a representation predicate $\mathrm{Rep}$ such that the three streaming functions meet `initSpec Rep`, `updateSpec Rep` and `finalSpec Rep`. Here $\mathrm{Rep}(a, st, key, m)$ relates the address $a$ of a 256-byte `crypto_onetimeauth_poly1305_state`, its bytes $st$, a key and a message:
--   - **init** (`x0 = state`, `x1 = key`): with 256 owned bytes at `state` and the 32 key bytes $key$ at `key`, it leaves 256 bytes $st'$ at `state` with $\mathrm{Rep}(\mathtt{state}, st', key, [\,])$, and the key unchanged. It uses no stack.
--   - **update** (`x0 = state`, `x1 = in`, `x2 = inlen`): with 256 owned bytes $st$ at `state` such that $\mathrm{Rep}(\mathtt{state}, st, key, m)$, the bytes $inp$ at `in` and `inlen` $= |inp|$, it leaves 256 bytes $st'$ with $\mathrm{Rep}(\mathtt{state}, st', key, m \mathbin{+\!\!+} inp)$, and $inp$ unchanged. It uses the 48 bytes below the stack pointer.
--   - **final** (`x0 = state`, `x1 = out`): with 256 owned bytes $st$ at `state` such that $\mathrm{Rep}(\mathtt{state}, st, key, m)$ and 16 owned bytes at `out`, it writes `poly1305Mac m key` (RFC 8439 §2.5.1) to `out`, sets the first 96 bytes of the state to zero and leaves the other 160 unchanged. It uses the 4144 bytes below the stack pointer.
--
--   Second, the one-shot `crypto_onetimeauth_poly1305_donna(out, m, inlen, key)` meets `oneshotSpec`: with 16 owned bytes at `out`, the bytes $m$ at `m`, `inlen` $= |m|$ and the 32 key bytes $key$ at `key`, with the stack-protector guard readable where the code reads it (`guardRes`), it writes `poly1305Mac m key` to `out` and leaves $m$, $key$ and the guard unchanged. It uses the 4320 bytes below the stack pointer.
--
--   `poly1305_donna.c`, lines 65–67, 78, 88 and 97: “poly1305_init(&state, key); poly1305_update(&state, m, inlen); poly1305_finish(&state, out);”, “poly1305_init((poly1305_state_internal_t *) (void *) state, key);”, “poly1305_update((poly1305_state_internal_t *) (void *) state, in, inlen);”, “poly1305_finish((poly1305_state_internal_t *) (void *) state, out);”.
-- source:
--   libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda), src/libsodium/crypto_onetimeauth/poly1305/donna/poly1305_donna.c lines 58–100 (the one-shot and init/update/final)

import Definitions.Def_Poly1305Debian_Spec

namespace Poly1305Debian

theorem internalOk_donna_init_update_final_oneshot :
    (∃ Rep : Poly1305Libsodium.StateRep, donnaInitOk Rep ∧ donnaUpdateOk Rep ∧ donnaFinalOk Rep) ∧
      donnaOneshotOk := by
  sorry

end Poly1305Debian
