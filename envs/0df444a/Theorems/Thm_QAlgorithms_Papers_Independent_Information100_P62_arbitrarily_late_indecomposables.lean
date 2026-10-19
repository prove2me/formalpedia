-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_arbitrarily_late_indecomposables
-- name    : QAlgorithms.Papers.Independent.Information100.P62.arbitrarily_late_indecomposables
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T21:57:47.865452+00:00
-- url     : https://prove2.me/theorems/4bcd0b30-26fe-4f50-a2c2-76927a446414
-- title:
--   Unnumbered consequence: arbitrarily late product-indecomposable types
-- statement:
--   Suppose the width sequence $w_n(\Phi)$ is not bounded eventually by any polynomial. Then
--   $$\forall N\ \exists n\ge N,\ n\ge2,\ \exists A\in\max\mathcal T(\Phi^{\otimes n}),\quad
--   A\notin\mathcal T(\Phi^{\otimes m})\star\mathcal T(\Phi^{\otimes(n-m)})\quad(1\le m<n).$$
--   Thus genuinely product-indecomposable maximal types occur at arbitrarily large block lengths.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 46, Unnumbered consequence: arbitrarily late product-indecomposable types

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.46, 56, Unnumbered consequence: arbitrarily late product-indecomposable types. -/
theorem arbitrarily_late_indecomposables [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F)
    (hsuper : ¬ ∃ C : ℝ, 0 < C ∧ ∃ p N : ℕ, ∀ n, N ≤ n → 1 ≤ n →
      (width F n : ℝ) ≤ C * (n : ℝ) ^ p) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ A : Shape, Indecomposable F n A := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
