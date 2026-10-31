-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P23_projectionDifference_kernel
-- name    : QAlgorithms.Papers.Independent.Intake100.P23.projectionDifference_kernel
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:15:39.30042+00:00
-- url     : https://prove2.me/theorems/02e58eb9-5245-47f2-95ee-5c444c98811e
-- title:
--   Kernel of a difference of orthogonal projections
-- statement:
--   Let $V_1,V_2$ be closed subspaces of a real or complex Hilbert space $F$, and let $P_1,P_2$ be their orthogonal projections, all over the same scalar field. Then
--   $$\ker(P_1-P_2)=(V_1\cap V_2)+(V_1^\perp\cap V_2^\perp).$$
--   The plus sign is the algebraic subspace sum, represented by the supremum in the lattice of linear subspaces. This elementary identity underlies the projection criteria for real subspaces of complex Hilbert spaces.
-- source:
--   Introduction to representations of the canonical commutation and anticommutation relations, arXiv:math-ph/0511030v2, PDF p. 60, Lemma 1: kernel of a difference of projections

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P23

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P23

open QAlgorithms.Papers.Independent.Renew46.P03 (tensorVector)

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Projections

/-- PDF p.60, Lemma 1: algebraic sum of intersections and the projection kernel.
The scalar field is the same for both complements and both projections. -/
theorem projectionDifference_kernel
    {K F : Type*} [RCLike K] [NormedAddCommGroup F] [InnerProductSpace K F] [CompleteSpace F]
    (V1 V2 : ClosedSubmodule K F) :
    (V1.toSubmodule ⊓ V2.toSubmodule) ⊔
        (V1.toSubmoduleᗮ ⊓ V2.toSubmoduleᗮ) =
      LinearMap.ker ((V1.toSubmodule.starProjection - V2.toSubmodule.starProjection).toLinearMap) := by sorry

end Projections

end QAlgorithms.Papers.Independent.Intake100.P23

end
