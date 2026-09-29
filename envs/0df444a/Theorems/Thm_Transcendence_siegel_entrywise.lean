-- Prove2me | Theorems.Thm_Transcendence_siegel_entrywise
-- name    : Transcendence.siegel_entrywise
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-27T07:58:09.795978+00:00
-- url     : https://prove2.me/theorems/be2108be-d4da-41d0-89c3-0a31d75bb6f8
-- title:
--   Siegel's lemma with an entrywise bound, for at least twice as many unknowns as equations
-- statement:
--   Let $A$ be an integer matrix with $m$ rows and $n \ge 1$ columns, where $2m \le n$, and suppose every entry satisfies $|A_{ab}| \le B$ for some real $B \ge 1$. Then there is a non-zero $t \in \mathbb{Z}^{n}$ with $At = 0$ and
--
--   $$|t_b| \le nB \quad \text{for every } b.$$
--
--   Mathlib's Siegel lemma (`Int.Matrix.exists_ne_zero_int_vec_norm_le`) bounds the solution by $(n \max(1, \|A\|))^{m/(n-m)}$; with at least twice as many unknowns as equations the exponent is at most one, and this is the linear form used by the auxiliary-function constructions of the four and six exponentials theorems.
-- source:
--   Siegel's lemma, as in S. Lang, Introduction to Transcendental Numbers (1966), ch. I §2, here in the form of Mathlib's `Int.Matrix.exists_ne_zero_int_vec_norm_le`. Formal proof: Diaz modulus mission, 27 September 2026 (C. Perassi).

import Mathlib

namespace Transcendence

theorem siegel_entrywise {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℤ)
    (hβ : 0 < Fintype.card β) (hcard : 2 * Fintype.card α ≤ Fintype.card β) {B : ℝ}
    (hB : 1 ≤ B) (hA : ∀ a b, |(A a b : ℝ)| ≤ B) :
    ∃ t : β → ℤ, t ≠ 0 ∧ (∀ a, ∑ b, A a b * t b = 0) ∧
      ∀ b, |(t b : ℝ)| ≤ Fintype.card β * B := by
  sorry

end Transcendence
