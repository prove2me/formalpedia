-- Prove2me | Theorems.Thm_Poly1305Boringssl_subroutineOk_init_update_finish
-- name    : Poly1305Boringssl.subroutineOk_init_update_finish
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-24T10:08:48.80787+00:00
-- url     : https://prove2.me/theorems/adeb3f39-004c-4f92-a5f7-e3ed1c4209f8
-- title:
--   poly1305.h — CRYPTO_poly1305_init, _update and _finish compute RFC 8439's Poly1305 tag
-- statement:
--   There is a representation predicate $\mathrm{Rep}$ such that the three exported functions of the AArch64 object code of BoringSSL's `poly1305.cc` (`boringsslPoly1305Lib`) meet their contracts `initSpec Rep`, `updateSpec Rep` and `finishSpec Rep`, each with total correctness under every placement of the library the linker could produce. In detail, for every entry state at the function with the stack pointer 16-byte aligned and every frame $R$ held separately, execution terminates and returns to the caller (the link register) with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding; it never panics, exits or runs out of memory. Here $\mathrm{Rep}(a, st, key, m)$ relates the address $a$ of a `poly1305_state` buffer, its 512 bytes $st$, a key and a message:
--   - **init** (`x0 = state`, `x1 = key`): with 512 owned bytes at `state` and 32 readable key bytes $key$ at `key`, it leaves 512 bytes $st'$ at `state` with $\mathrm{Rep}(\mathtt{state}, st', key, [\,])$, and the key unchanged.
--   - **update** (`x0 = state`, `x1 = in`, `x2 = in_len`): with 512 owned bytes $st$ at `state` such that $\mathrm{Rep}(\mathtt{state}, st, key, m)$, the bytes $inp$ readable at `in` and `in_len` $= |inp|$, it leaves 512 bytes $st'$ with $\mathrm{Rep}(\mathtt{state}, st', key, m \mathbin{+\!\!+} inp)$, and $inp$ unchanged. It uses the 64 bytes below the stack pointer.
--   - **finish** (`x0 = state`, `x1 = mac`): with 512 owned bytes $st$ at `state` such that $\mathrm{Rep}(\mathtt{state}, st, key, m)$ and 16 owned bytes at `mac`, it writes `poly1305Mac m key` (RFC 8439 §2.5.1) to `mac` and leaves some 512 bytes at `state`. It uses the 48 bytes below the stack pointer.
--
--   The buffer, the key, the input, the tag and the stack frame are pairwise disjoint (separating conjunction). Chaining the three contracts: after `CRYPTO_poly1305_init(state, key)`, any number $k \ge 0$ of calls `CRYPTO_poly1305_update(state, in_j, len_j)` and `CRYPTO_poly1305_finish(state, mac)`, all on the same `state`, `mac` holds `poly1305Mac` of the concatenation of the inputs, with the key.
--
--   poly1305.h, lines 30–33, 37–38 and 42–43: “CRYPTO_poly1305_init sets up \`state\` so that it can be used to calculate an authentication tag with the one-time key \`key\`. Note that \`key\` is a one-time key and therefore there is no \`reset' method because that would enable several messages to be authenticated with the same key.” “CRYPTO_poly1305_update processes \`in_len\` bytes from \`in\`. It can be called zero or more times after poly1305_init.” “CRYPTO_poly1305_finish completes the poly1305 calculation and writes a 16 byte authentication tag to \`mac\`.”
-- source:
--   BoringSSL commit f8b3e2347647a6ad8d26e2ce4cee34f792d5f880 (https://boringssl.googlesource.com/boringssl/+/f8b3e2347647a6ad8d26e2ce4cee34f792d5f880), include/openssl/poly1305.h lines 30–45 (CRYPTO_poly1305_init, CRYPTO_poly1305_update, CRYPTO_poly1305_finish)

import Definitions.Def_Poly1305Boringssl_Spec

namespace Poly1305Boringssl

theorem subroutineOk_init_update_finish :
    ∃ Rep : StateRep, initOk Rep ∧ updateOk Rep ∧ finishOk Rep := by
  sorry

end Poly1305Boringssl
