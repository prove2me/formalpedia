-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P02_diagonal_inverse_averages
-- name    : QAlgorithms.Papers.Independent.Frontier30.P02.diagonal_inverse_averages
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:11:47.878095+00:00
-- url     : https://prove2.me/theorems/a40a45b4-93d2-4bce-8651-cf4ed12d0d8b
-- title:
--   A diagonal matrix as two simultaneous inverse averages
-- statement:
--   Let $n>0$ and $D=\operatorname{diag}(d_1,\ldots,d_n)$ be a real diagonal matrix with $d_j\ge1$ for every $j$. There are real diagonal matrices $D_1,D_2$, each with strictly positive diagonal entries, such that
--
--   $$
--   D=\frac{D_1+D_2}{2}=\frac{D_1^{-1}+D_2^{-1}}{2}.
--   $$
--
--   The inverses are genuine inverses. This simultaneous averaging identity is used in the two-Gram representation of Gaussian covariances.
--
--   **Formalization Note** Diagonal matrices are represented by their full functions of diagonal entries; each equality is imposed at every coordinate.
-- source:
--   The Symmetry Group of Gaussian States in $L^2 (\mathbb{R}^n)$, arXiv:1101.5041v1, PDF p. 10, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P02

noncomputable section

open scoped ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify)

namespace QAlgorithms.Papers.Independent.Frontier30.P02

/-- Lemma 1, arXiv:1101.5041v1, PDF p.10: both diagonal averages.
Functions denote the complete diagonal, and positivity guards every reciprocal. -/
theorem diagonal_inverse_averages {n : ℕ} (hn : 0 < n) (d : Fin n → ℝ)
    (hd : ∀ j, 1 ≤ d j) :
    ∃ d1 d2 : Fin n → ℝ,
      (∀ j, 0 < d1 j) ∧ (∀ j, 0 < d2 j) ∧
      (∀ j, d j = (d1 j + d2 j) / 2) ∧
      (∀ j, d j = ((d1 j)⁻¹ + (d2 j)⁻¹) / 2) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P02

end
