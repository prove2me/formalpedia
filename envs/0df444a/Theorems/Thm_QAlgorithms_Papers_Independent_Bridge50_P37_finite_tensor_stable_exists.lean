-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_finite_tensor_stable_exists
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.finite_tensor_stable_exists
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:35:56.883196+00:00
-- url     : https://prove2.me/theorems/eeecb022-624b-44a7-84c1-a89592c3e00d
-- title:
--   Theorem 1: existence of nontrivial n-tensor-stable positive maps
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. CP means completely positive, coCP means that output transposition composed with the map is CP, and nontrivial means neither. Tensor-stable positivity means positivity at every positive tensor degree.
--
--   For every positive integer $n$ and dimensions $d_1,d_2\ge2$, there exists a positive map $P:M_{d_1}\to M_{d_2}$ such that
--   $$P^{\otimes n}\text{ is positive},\qquad P\text{ is neither CP nor coCP}.$$
--   The map can depend on $n,d_1,d_2$. This is finite-degree existence, with no assertion that one nontrivial map works at every degree.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 2, Theorem 1: existence of nontrivial n-tensor-stable positive maps

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P37

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

-- Only the following exact definition bodies are reused from pinned accepted papers.

open QAlgorithms.Papers.Independent.Information100.P04 (gamma copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap IsPositiveMap)

open QAlgorithms.Papers.Independent.Information100.P50 (maxEigenvalue)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

namespace QAlgorithms.Papers.Independent.Bridge50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Theorem 1, PDF p.2, construction pp.6--7: the map may depend on n and both dimensions. -/
theorem finite_tensor_stable_exists (n d1 d2 : ℕ) (hn : 0 < n)
    (h1 : 2 ≤ d1) (h2 : 2 ≤ d2) :
    ∃ P : MatrixMap (Fin d1) (Fin d2), NTensorStable P n ∧ Nontrivial P := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
