-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_row_coefficient_identities
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.row_coefficient_identities
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:25:19.041958+00:00
-- url     : https://prove2.me/theorems/e79e9f62-0788-4724-8d7a-e12d2d4be3a2
-- title:
--   Remark 6.2: row coefficient identities
-- statement:
--   Let $U\in SO(3)$ have entries in $\mathbb D[\sqrt2]$, represented as $U_{ij}=(A_{ij}+B_{ij}\sqrt2)/(\sqrt2)^k$ with integer matrices $A,B$ and any natural common denominator exponent $k$. The row analogues of Lemma 6.1 hold: for every row pair $i,\ell$,
--
--   $$
--   \sum_j(A_{ij}B_{\ell j}+B_{ij}A_{\ell j})=0,\qquad
--   \sum_j(A_{ij}A_{\ell j}+2B_{ij}B_{\ell j})=2^k\delta_{i\ell}.
--   $$
--   For each row $i$ this also gives $\sum_j A_{ij}B_{ij}=0$ and $\sum_j(A_{ij}^2+2B_{ij}^2)=2^k$.
--
--   All these properties are conclusions about orthogonal matrices, rather than extra premises.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 6, Remark 6.2: row coefficient identities

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Remark 6.2, PDF p.6: all the analogous row identities are conclusions,
not added assumptions about the matrix. -/
theorem row_coefficient_identities (U : RealMat) (hU : SpecialOrthogonal U)
    (hring : ∀ i j, InDsqrt2 (U i j)) (k : ℕ)
    (A B : Matrix (Fin 3) (Fin 3) ℤ)
    (hcoeff : ∀ i j, U i j = ((A i j : ℝ) + (B i j : ℝ) * Real.sqrt 2) / (Real.sqrt 2) ^ k) :
    (∀ i l,
      (∑ j, (A i j * B l j + B i j * A l j)) = 0 ∧
      (∑ j, (A i j * A l j + 2 * (B i j * B l j))) =
        (2 : ℤ) ^ k * (if i = l then 1 else 0)) ∧
    (∀ i, (∑ j, A i j * B i j) = 0 ∧
      (∑ j, (A i j ^ 2 + 2 * B i j ^ 2)) = (2 : ℤ) ^ k) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
