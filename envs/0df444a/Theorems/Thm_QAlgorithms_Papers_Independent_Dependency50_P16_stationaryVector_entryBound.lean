-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_stationaryVector_entryBound
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.stationaryVector_entryBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:17:59.593847+00:00
-- url     : https://prove2.me/theorems/a815d4c4-5c86-4c42-a0f9-f945c4a612f2
-- title:
--   Lemma 3.9: Stationary-vector entry bound
-- statement:
--   Let $A\in\mathbb R^{n\times n}$ have nonpositive diagonal and nonnegative off-diagonal entries, and let $v\in\mathbb R^n$ satisfy $v_i\ge0$ and $Av=0$. Then
--
--   $$A_{ij}v_j\le\|A\|_{\max}v_i\qquad(i\ne j),\qquad \|A\|_{\max}=\max_{i,j}|A_{ij}|.$$
--
--   No normalization of $v$ or column-sum assumption on $A$ is required. The bound controls individual stationary flows.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 10, Lemma 3.9: Stationary-vector entry bound

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

local notation "Mat" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ

local notation "Vec" => fun n : ℕ => Fin n → ℝ

local notation "Hilbert" => fun n : ℕ => EuclideanSpace ℂ (Fin n)

local notation "Operator" => fun n : ℕ => Module.End ℂ (Mat n)

/-- arXiv:2308.00561v1, PDF p.10, Lemma 3.9: Stationary-vector entry bound. An explicit finite NNReal supremum gives exactly the maximum absolute entry. v=0 is source-allowed and yields 0 <= 0. -/
theorem stationaryVector_entryBound {n : ℕ} (hn : 2 ≤ n) (A : RMat n) (v : Vec n)
    (hdiag : ∀ i, A i i ≤ 0) (hoff : ∀ i j, i ≠ j → 0 ≤ A i j)
    (hv : ∀ i, 0 ≤ v i) (hAv : A *ᵥ v = 0) :
    ∀ i j, i ≠ j → A i j * v j ≤ maxEntryNorm A * v i := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
