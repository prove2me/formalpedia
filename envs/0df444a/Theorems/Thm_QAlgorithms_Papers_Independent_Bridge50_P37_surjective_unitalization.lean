-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_surjective_unitalization
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.surjective_unitalization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:45:21.847299+00:00
-- url     : https://prove2.me/theorems/426128d3-afa0-4260-8030-c559342c8425
-- title:
--   Unnumbered right-inverse-bound preparation: surjective positive map can be unitalized
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. CP means completely positive, coCP means that output transposition composed with the map is CP, and nontrivial means neither. Tensor-stable positivity means positivity at every positive tensor degree.
--
--   Let $R:M_{d_3}\to M_{d_2}$ be surjective, tensor-stable positive and not CP. Then $R(I_{d_3})$ is positive definite. Define
--   $$P(X)=R(I_{d_3})^{-1/2}R(X)R(I_{d_3})^{-1/2}.$$
--   This actual filtered map is unital, surjective and tensor-stable positive, and
--   $$P\text{ is CP}\iff R\text{ is CP},\qquad P\text{ is coCP}\iff R\text{ is coCP}.$$
--   Strict positivity of $R(I)$ is a conclusion; the filter is not an arbitrary witness.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 9, Unnumbered right-inverse-bound preparation: surjective positive map can be unitalized

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

/-- Unnumbered unitalization, PDF p.9: R(I)>0 is concluded, and the filter is constructed. -/
theorem surjective_unitalization [Nonempty A] [Nonempty B] (R : MatrixMap A B)
    (hR : TensorStable R) (hs : Function.Surjective R)
    (hncp : ¬ Entanglement.IsCompletelyPositive R) :
    (R 1).PosDef ∧ unitalize R 1 = 1 ∧ Function.Surjective (unitalize R) ∧
    TensorStable (unitalize R) ∧
    (Entanglement.IsCompletelyPositive (unitalize R) ↔ Entanglement.IsCompletelyPositive R) ∧
    (OutputCoPositive (unitalize R) ↔ OutputCoPositive R) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
