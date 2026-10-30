-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_trivial_classes_tensor_stable
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.trivial_classes_tensor_stable
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:41:56.383208+00:00
-- url     : https://prove2.me/theorems/0510e6f2-3fea-43ee-a16f-9bbd187340d7
-- title:
--   Example I.1: the two trivial classes are tensor-stable
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. CP means completely positive, coCP means that output transposition composed with the map is CP, and nontrivial means neither. Tensor-stable positivity means positivity at every positive tensor degree.
--
--   For every completely positive map $T:M_{d_1}\to M_{d_2}$,
--   $$T\text{ and }\vartheta_{d_2}\circ T\text{ are tensor-stable positive}.$$
--   The latter are exactly the completely co-positive maps. Neither class is restricted to trace-preserving maps. This identifies the two trivial families used throughout the paper.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 2, Example I.1: the two trivial classes are tensor-stable

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

/-- Example I.1, PDF p.2: CP and output-transpose-after-CP are tensor-stable, without TP. -/
theorem trivial_classes_tensor_stable [Nonempty A] [Nonempty B] (T : MatrixMap A B)
    (hT : Entanglement.IsCompletelyPositive T) :
    TensorStable T ∧ TensorStable ((basisTransposeLinearMap B).comp T) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
