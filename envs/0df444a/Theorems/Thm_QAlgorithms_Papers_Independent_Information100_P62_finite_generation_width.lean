-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_finite_generation_width
-- name    : QAlgorithms.Papers.Independent.Information100.P62.finite_generation_width
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T21:56:43.907137+00:00
-- url     : https://prove2.me/theorems/1567a383-c391-48cc-b2be-04f0fbb18c73
-- title:
--   Lemma 5.3: finite generation gives polynomial width
-- statement:
--   Fix maximal transmittable generators $G_1,\ldots,G_R$ for $\Phi$ at positive lengths $\ell_1,\ldots,\ell_R$. Suppose every maximal algebra at each $n\ge1$ embeds in $\bigotimes_jG_j^{\otimes a_j}$ for some nonnegative integers $a_j$ with $\sum_ja_j\ell_j=n$. Then
--   $$w_n(\Phi)\le\binom{n+R}{R}=O(n^R).$$
--   The asymptotic constant may depend on the fixed generating family, and is chosen before $n$. This obstructs finite generation when width grows superpolynomially.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 46, Lemma 5.3: finite generation gives polynomial width

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.46, Lemma 5.3: finite generation gives polynomial width. -/
theorem finite_generation_width [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (R : ℕ) (hR : 0 < R)
    (G : Fin R → Shape) (ell : Fin R → ℕ) (hell : ∀ j, 0 < ell j)
    (hG : ∀ j, Maximal (tensorPower F (ell j)) (G j))
    (hgen : ∀ n, 1 ≤ n → ∀ A, Maximal (tensorPower F n) A →
      ∃ a : Fin R → ℕ, (∑ j, a j * ell j) = n ∧ Embeds A (generatedProduct G a)) :
    (∀ n, 1 ≤ n → width F n ≤ Nat.choose (n + R) R) ∧
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n, N ≤ n → 1 ≤ n → (width F n : ℝ) ≤ C * (n : ℝ) ^ R := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
