-- Prove2me | Theorems.Thm_Poly1305_clamped_card_and_form
-- name    : Poly1305.clamped_card_and_form
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-24T07:39:28.587215+00:00
-- url     : https://prove2.me/theorems/cd933399-12cf-45f0-99db-81f1f83109dc
-- title:
--   §2 — there are 2^106 possibilities for r, of the form r₀ + r₁ + r₂ + r₃
-- statement:
--   The set of natural numbers $r[0] + 2^8 r[1] + \dots + 2^{120} r[15]$ over 16-byte strings satisfying the conditions of p. 4 (`IsClamped`) has exactly $2^{106}$ elements; and a natural number $n$ is of that form if and only if $n = r_0 + r_1 + r_2 + r_3$ with $r_0 \in \{0, 1, \dots, 2^{28} - 1\}$ and $r_1/2^{32}$, $r_2/2^{64}$, $r_3/2^{96}$ each in $\{0, 4, 8, \dots, 2^{28} - 4\}$ (written as $r_1 = 2^{32} \cdot 4k$ with $k < 2^{26}$, and likewise).
-- source:
--   Bernstein, D. J., The Poly1305-AES message-authentication code, in: Fast Software Encryption (FSE 2005), Lecture Notes in Computer Science 3557, Springer, 2005, 32–49, https://doi.org/10.1007/11502760_3 (author's version of 2005-03-29: https://cr.yp.to/mac/poly1305-20050329.pdf), p. 4, §2, Keys (the 2^106 possibilities for r)

import Mathlib.Data.Set.Card
import Definitions.Def_Poly1305Bernstein

namespace Poly1305

theorem clamped_card_and_form :
    {n : ℕ | ∃ r : Str16, IsClamped r ∧ leVal r = n}.ncard = 2 ^ 106 ∧
    ∀ n : ℕ, (∃ r : Str16, IsClamped r ∧ leVal r = n) ↔
      ∃ r₀ r₁ r₂ r₃ : ℕ, n = r₀ + r₁ + r₂ + r₃ ∧ r₀ < 2 ^ 28 ∧
        (∃ k ∈ Finset.range (2 ^ 26), r₁ = 2 ^ 32 * (4 * k)) ∧
        (∃ k ∈ Finset.range (2 ^ 26), r₂ = 2 ^ 64 * (4 * k)) ∧
        (∃ k ∈ Finset.range (2 ^ 26), r₃ = 2 ^ 96 * (4 * k)) := by
  sorry

end Poly1305
