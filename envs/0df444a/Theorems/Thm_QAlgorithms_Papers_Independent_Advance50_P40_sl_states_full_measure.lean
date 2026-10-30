-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P40_sl_states_full_measure
-- name    : QAlgorithms.Papers.Independent.Advance50.P40.sl_states_full_measure
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:05:09.328669+00:00
-- url     : https://prove2.me/theorems/385f65b0-b959-433a-98fc-1750fff8dda0
-- title:
--   SL states have full measure among bipartite density matrices
-- statement:
--   Fix positive finite dimensions $n,m$ and a system orthonormal basis. For a joint matrix $\rho$, let $B_{ij}(\rho)=(\rho_{(i,a),(j,b)})_{a,b=1}^m$ be its bath-valued system block. Say that a density matrix is SL in this basis if each block is zero or has nonzero trace. Let $\mathcal D_{nm}$ be the positive semidefinite trace-one matrices and let $\lambda$ be Lebesgue measure on the real affine space of Hermitian trace-one matrices. Then
--   $$
--   \lambda\!\left(\{\rho\in\mathcal D_{nm}:\exists i,j,\ B_{ij}(\rho)\ne0\ \text{and}\ \operatorname{Tr}B_{ij}(\rho)=0\}\right)=0.
--   $$
--   This is a measure statement for intrinsic SL membership of actual density matrices, rather than genericity of a redundant expansion.
--
--   **Formalization Note** The real affine space has dimension $d=(nm)^2-1$. Lean uses $d$-dimensional Hausdorff measure on the matrix metric restricted to the exceptional set. On this finite-dimensional affine space its null sets are precisely the Lebesgue null sets. A zero bath block is allowed, and at $n=m=1$ the exceptional set is empty.
-- source:
--   Vanishing quantum discord is necessary and sufficient for completely positive maps, arXiv:0808.0175v2, PDF p. 1, Introduction; Discussion on PDF p.4

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P40

open scoped Matrix.Norms.Frobenius

/-- Full-measure claim, PDF p. 1, pinned to the hyperplane argument on PDF p. 4.
The real affine space of Hermitian trace-one joint matrices has dimension
(n*m)^2-1. Hausdorff measure in that dimension, restricted to this affine
space, has exactly its Lebesgue null sets. The measurable structure is explicitly
the Borel sigma-algebra of the Frobenius matrix metric. This is not ambient complex-matrix
volume. At n=m=1 the dimension is zero and the exceptional set is empty. -/
theorem sl_states_full_measure (n m : ℕ) [NeZero n] [NeZero m] :
    letI jointMetric : EMetricSpace (JointMatrix n m) := inferInstance
    letI jointMeasurable : MeasurableSpace (JointMatrix n m) :=
      @borel (JointMatrix n m) jointMetric.toUniformSpace.toTopologicalSpace
    (@MeasureTheory.Measure.hausdorffMeasure (JointMatrix n m)
      jointMetric jointMeasurable ⟨rfl⟩ (((n * m) ^ 2 - 1 : ℕ) : ℝ))
      {rho | QAlgorithms.IsDensityMatrix rho ∧ ¬ IsSLState rho} = 0 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P40

end
