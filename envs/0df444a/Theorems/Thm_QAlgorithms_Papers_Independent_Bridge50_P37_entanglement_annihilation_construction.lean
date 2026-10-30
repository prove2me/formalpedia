-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_entanglement_annihilation_construction
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.entanglement_annihilation_construction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:42:47.755138+00:00
-- url     : https://prove2.me/theorems/05d9511f-983f-4501-8a39-b6f77cb44967
-- title:
--   Theorem 5: entanglement annihilation produces a nontrivial tensor-stable map
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. CP means completely positive, coCP means that output transposition composed with the map is CP, and nontrivial means neither. Tensor-stable positivity means positivity at every positive tensor degree.
--
--   Let $T:M_{d_1}\to M_{d_2}$ be a channel that is not entanglement breaking. A single positive map $S:M_{d_2}\to M_{d_1}$ can be chosen so that, with
--   $$P=(S\circ T)\otimes(\vartheta_{d_1}\circ S\circ T),$$
--   for every $k\ge2$ for which $T^{\otimes k}$ sends every positive input to a fully $k$-partite separable output, $P$ is $\lfloor k/2\rfloor$-tensor-stable positive and neither CP nor coCP. If the same $T$ annihilates entanglement for every positive $k$, the same construction gives one nontrivial tensor-stable positive $P$. Its input and output dimension is $d_1^2$.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 7, Theorem 5: entanglement annihilation produces a nontrivial tensor-stable map

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

/-- Theorem 5, PDF pp.7--8: finite k and the all-degree implication.
The infinite-degree witness S is chosen once for T, before every tensor degree. -/
theorem entanglement_annihilation_construction [Nonempty A] [Nonempty B] (T : MatrixMap A B)
    (hT : IsChannel T) (hEB : ¬ RectangularEBPositive T) :
    ∃ S : MatrixMap B A, IsPositiveMap S ∧
      (∀ k : ℕ, 2 ≤ k → LocallyEA T k →
        NTensorStable (tensorLinearMap (S.comp T) ((basisTransposeLinearMap A).comp (S.comp T))) (k/2) ∧
        Nontrivial (tensorLinearMap (S.comp T) ((basisTransposeLinearMap A).comp (S.comp T)))) ∧
      (InfinityEA T → TensorStable (tensorLinearMap (S.comp T) ((basisTransposeLinearMap A).comp (S.comp T))) ∧
        Nontrivial (tensorLinearMap (S.comp T) ((basisTransposeLinearMap A).comp (S.comp T)))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
