-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_cp_processed_zero_two_way
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.cp_processed_zero_two_way
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:52:26.897603+00:00
-- url     : https://prove2.me/theorems/b7b7b23c-fa43-44f8-b706-79455687aa8b
-- title:
--   Corollary 2: CP-processed tensor-stable positive maps yield zero two-way capacity
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. CP means completely positive, coCP means that output transposition composed with the map is CP, and nontrivial means neither. Tensor-stable positivity means positivity at every positive tensor degree.
--
--   Let $P:M_a\to M_b$ be tensor-stable positive and not CP. Suppose $T:M_{d_1}\to M_{d_2}$ is a channel with a finite representation
--   $$T=\sum_j V_j\circ P\circ W_j,$$
--   where $W_j:M_{d_1}\to M_a$ and $V_j:M_b\to M_{d_2}$ are arbitrary CP maps. Then
--   $$Q_2(T)=0.$$
--   This is a structural representation hypothesis on the actual channel. No inverse of $P$ and no zero-capacity assumption is required. The displayed composition fixes the preprocessing/postprocessing convention despite reversed domain declarations in the preceding prose.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 16, Corollary 2: CP-processed tensor-stable positive maps yield zero two-way capacity

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

/-- Corollary 2, PDF p.16: W is preprocessing and V postprocessing, as fixed by the
source's displayed composition (the preceding prose reverses their domain declarations). -/
theorem cp_processed_zero_two_way (d1 d2 d3 d4 : ℕ)
    [NeZero d1] [NeZero d2] [NeZero d3] [NeZero d4]
    (T : MatrixMap (Fin d1) (Fin d2)) (P : MatrixMap (Fin d3) (Fin d4))
    (hT : IsChannel T) (hP : TensorStable P) (hncp : ¬ Entanglement.IsCompletelyPositive P)
    (m : ℕ) (V : Fin m → MatrixMap (Fin d4) (Fin d2)) (W : Fin m → MatrixMap (Fin d1) (Fin d3))
    (hVW : ∀ i, Entanglement.IsCompletelyPositive (V i) ∧ Entanglement.IsCompletelyPositive (W i))
    (hrep : T = ∑ i, (V i).comp (P.comp (W i))) : diamondAssistedCapacity T false = 0 := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
