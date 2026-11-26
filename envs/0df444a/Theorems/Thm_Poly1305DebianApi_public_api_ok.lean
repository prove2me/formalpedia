-- Prove2me | Theorems.Thm_Poly1305DebianApi_public_api_ok
-- name    : Poly1305DebianApi.public_api_ok
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-26T11:24:25.666919+00:00
-- url     : https://prove2.me/theorems/4c0f9f4a-79c3-57d4-b1a2-e9f86d4ce8af
-- title:
--   Debian's libsodium Poly1305 API is correct: crypto_onetimeauth*, crypto_onetimeauth_poly1305*, crypto_verify_16/32/64 (AArch64)
-- statement:
--   libsodium documentation, *Secret-key single-message authentication using Poly1305*, lines 65, 72, 74, 94, 98, 100 and 110: “The `crypto_onetimeauth()` function authenticates a message `in` whose length is `inlen` using a secret key `k` (`crypto_onetimeauth_KEYBYTES` bytes) and puts the authenticator into `out` (`crypto_onetimeauth_BYTES` bytes).” “The `crypto_onetimeauth_verify()` function verifies, in constant time, that `h` is a correct authenticator for the message `in` whose length is `inlen` bytes, using the secret key `k`.” “It returns `-1` if the verification fails, or `0` on success.” “The `crypto_onetimeauth_init()` function initializes a structure pointed by `state` using a key `key`.” “`crypto_onetimeauth_update()` can then be called more than once in order to compute the authenticator from sequential chunks of the message.” “Finally, `crypto_onetimeauth_final()` puts the authenticator into `out`.” “The `crypto_onetimeauth_keygen()` function fills `k` with a random key.”
--
--   The statement: every public function in Debian's AArch64 object code of libsodium 1.0.22's one-time authentication and `crypto_verify` (the objects of `crypto_onetimeauth.c`, `onetimeauth_poly1305.c`, `poly1305_donna.c` and `crypto_verify/verify.c` from Debian's `libsodium.a`, unmodified, linked into one library, `libsodiumDebianOnetimeauthCtLib`) meets its contract (bundle `Poly1305DebianApi_Spec`). Each claim is total correctness of a symbol of the code block under every placement of the library the linker could produce that treats every GOT access to `__stack_chk_guard` alike (`GuardUniform`), and every hook table laid out as a real link lays it out (`Link.PlacedLib.LinkOk`) whose hooks for `sodium_memzero` and `memset` meet `Libc.explicitBzeroSpec` and `VerifiedLibraries.Musl.cryptoMemsetSpec` (`dataOk`). In detail, take every entry state at the function with the stack pointer 16-byte aligned, the library's data objects in their initial state (the pointer `implementation`, the function-pointer table, the string `"poly1305"` and `optblocker_u16`, `PlacedLib.dataInit`), and every frame $R$ held separately. Execution terminates and returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched, the data objects unchanged and the postcondition holding; it never panics, exits or runs out of memory. Inputs may be owned or read-only memory, and they, the state, the outputs, the data objects and the stack frame are pairwise disjoint (separating conjunction).
--
--   - **Streaming.** There is a representation predicate $\mathrm{Rep}$, relating the address of a 256-byte state, its bytes, a key and the message so far, such that `crypto_onetimeauth_init` and `crypto_onetimeauth_poly1305_init` meet `initSpec Rep`, `crypto_onetimeauth_update` and `crypto_onetimeauth_poly1305_update` meet `updateSpec Rep`, and `crypto_onetimeauth_final` and `crypto_onetimeauth_poly1305_final` meet `finalSpec Rep`: `_init(state, key)` leaves a state with $\mathrm{Rep}(\mathtt{state}, st', key, [\,])$; `_update(state, in, inlen)` turns $\mathrm{Rep}(\mathtt{state}, st, key, m)$ into $\mathrm{Rep}(\mathtt{state}, st', key, m \mathbin{+\!\!+} inp)$ for the `inlen` bytes $inp$ at `in`; `_final(state, out)` writes `poly1305Mac m key` (RFC 8439 §2.5.1) to `out` and zeroes the first 96 state bytes. Each returns `0` in `w0`; they use no stack, 48 and 4144 bytes below the stack pointer. One $\mathrm{Rep}$ serves both names, so a state may be set up with one and continued with the other.
--   - **One-shot.** `crypto_onetimeauth` and `crypto_onetimeauth_poly1305` meet `oneshotSpec`: `(out, in, inlen, k)` writes `poly1305Mac m key` to the 16 bytes at `out` and returns `0`, using 4320 bytes of stack and reading the stack-protector guard (`guard`).
--   - **Verification.** `crypto_onetimeauth_verify` and `crypto_onetimeauth_poly1305_verify` meet `verifySpec`: `(h, in, inlen, k)` returns `0` in `w0` if the 16 bytes at `h` equal `poly1305Mac m key` and `-1` otherwise, changing nothing, using 4352 bytes of stack and reading the guard.
--   - **Comparison.** `crypto_verify_16`, `crypto_verify_32` and `crypto_verify_64` meet `verifyNSpec n`: `(x, y)` returns `0` if the $n$ bytes at `x` and `y` are equal and `-1` otherwise, changing nothing, using 32 bytes of stack.
--   - **Key generation.** For every property $R(n, bs)$ of a requested length and a byte string, if the hook for `randombytes_buf` meets `randombytesSpec R` (a C function that fills its buffer, `x0`, of length $n$ = `x1`, with bytes $bs$ such that $R(n, bs)$), then `crypto_onetimeauth_keygen` and `crypto_onetimeauth_poly1305_keygen` meet `keygenSpec R`: `(k)` leaves 32 bytes $bs$ with $R(32, bs)$ at `k`, using the 4096 bytes of stack the hook may use (`keygenOk`). So whatever `randombytes_buf` guarantees of a 32-byte output, the key has.
--   - **Constants.** `crypto_onetimeauth_bytes` and `crypto_onetimeauth_poly1305_bytes` return 16, `_keybytes` 32, `_statebytes` 256, and `crypto_verify_16_bytes`, `_32_bytes`, `_64_bytes` return 16, 32, 64, in `x0` (`constOk`); `crypto_onetimeauth_primitive` returns the address of the library's read-only data object `primitiveSym`, whose bytes are those of the C string `"poly1305"` (`primitiveSpec`).
-- source:
--   libsodium documentation, Secret-key single-message authentication using Poly1305 (https://doc.libsodium.org/advanced/poly1305; source jedisct1/libsodium-doc, commit 5adaf345, https://github.com/jedisct1/libsodium-doc/blob/5adaf34515b79d0b37bd8edbe042f20f3bdba2c6/advanced/poly1305.md), lines 65–74 and 94–110 (crypto_onetimeauth, _verify, _init, _update, _final, _keygen), implemented by the objects of Debian libsodium 1.0.22-2 (arm64), libsodium-dev_1.0.22-2_arm64.deb (https://deb.debian.org/debian/pool/main/libs/libsodium/libsodium-dev_1.0.22-2_arm64.deb), libsodium.a (crypto_onetimeauth.c, onetimeauth_poly1305.c, poly1305_donna.c and crypto_verify/verify.c of libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda)), with the constant getters and crypto_verify_16, _32, _64

import Definitions.Def_Poly1305DebianApi_Spec

namespace Poly1305DebianApi

theorem public_api_ok :
    (∃ Rep : Poly1305Libsodium.StateRep,
      initOk Rep "crypto_onetimeauth_init" ∧ updateOk Rep "crypto_onetimeauth_update" ∧
        finalOk Rep "crypto_onetimeauth_final" ∧
        initOk Rep "crypto_onetimeauth_poly1305_init" ∧
        updateOk Rep "crypto_onetimeauth_poly1305_update" ∧
        finalOk Rep "crypto_onetimeauth_poly1305_final") ∧
      oneshotOk "crypto_onetimeauth" ∧ oneshotOk "crypto_onetimeauth_poly1305" ∧
      verifyOk "crypto_onetimeauth_verify" ∧ verifyOk "crypto_onetimeauth_poly1305_verify" ∧
      keygenOk "crypto_onetimeauth_keygen" ∧ keygenOk "crypto_onetimeauth_poly1305_keygen" ∧
      dataOk "crypto_verify_16" (fun _ => verifyNSpec 16) ∧
      dataOk "crypto_verify_32" (fun _ => verifyNSpec 32) ∧
      dataOk "crypto_verify_64" (fun _ => verifyNSpec 64) ∧
      constOk "crypto_onetimeauth_bytes" 16 ∧ constOk "crypto_onetimeauth_keybytes" 32 ∧
      constOk "crypto_onetimeauth_statebytes" 256 ∧ constOk "crypto_onetimeauth_poly1305_bytes" 16 ∧
      constOk "crypto_onetimeauth_poly1305_keybytes" 32 ∧
      constOk "crypto_onetimeauth_poly1305_statebytes" 256 ∧
      constOk "crypto_verify_16_bytes" 16 ∧ constOk "crypto_verify_32_bytes" 32 ∧
      constOk "crypto_verify_64_bytes" 64 ∧
      dataOk "crypto_onetimeauth_primitive" primitiveSpec := by
  sorry

end Poly1305DebianApi
