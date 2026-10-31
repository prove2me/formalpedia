-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P17_frechet_inclusion_continuous
-- name    : QAlgorithms.Papers.Independent.Intake100.P17.frechet_inclusion_continuous
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:28:08.7535+00:00
-- url     : https://prove2.me/theorems/71bac630-6923-4153-8b1d-70749522870e
-- title:
--   Frechet subspace inclusions are continuous
-- statement:
--   Let \(K\) be either \(\mathbb R\) or \(\mathbb C\). Let \(X\) be a Hausdorff topological vector space over \(K\), and let \(F_1\subseteq F_2\subseteq X\) be \(K\)-linear subspaces. Give each \(F_j\) its own complete metrizable locally convex topology, and suppose the two inclusions \(j_j:F_j\to X\) are continuous. Then the inclusion \(i:F_1\to F_2\) satisfies
--   \[
--   \text{\(i\) is continuous.}
--   \]
--   The two Frechet topologies need not be inherited from \(X\).
--
--   This allows comparison of independently constructed smooth-vector topologies. **Formalization Note** Injective continuous linear maps into a common Hausdorff space express the subspace inclusions, with \(j_2i=j_1\). Local convexity uses the real scalar restrictions of the vector spaces over \(K\); the additive uniform structures are compatible and complete.
-- source:
--   Reflection Positivity and Conformal Symmetry, arXiv:1206.2039v2, PDF p. 34, Lemma 5.11

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P17

noncomputable section

open scoped BigOperators Topology

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Intake100.P17

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

/-- Lemma 5.11, PDF p. 34: Frechet topologies are represented independently on F1 and F2.
The Hausdorff hypothesis on X makes limits unique; no subspace topology is assumed.
The scalar field K ranges over the real and complex cases; real scalar structures
are compatible restrictions. The source imposes no complex-only restriction. -/
theorem frechet_inclusion_continuous
    {K : Type*} [RCLike K] {X F1 F2 : Type*}
    [AddCommGroup X] [Module K X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul K X] [T2Space X]
    [AddCommGroup F1] [Module K F1] [Module ℝ F1] [IsScalarTower ℝ K F1] [UniformSpace F1] [IsUniformAddGroup F1]
    [T2Space F1] [CompleteSpace F1] [TopologicalSpace.MetrizableSpace F1]
    [ContinuousSMul K F1] [ContinuousSMul ℝ F1] [LocallyConvexSpace ℝ F1]
    [AddCommGroup F2] [Module K F2] [Module ℝ F2] [IsScalarTower ℝ K F2] [UniformSpace F2] [IsUniformAddGroup F2]
    [T2Space F2] [CompleteSpace F2] [TopologicalSpace.MetrizableSpace F2]
    [ContinuousSMul K F2] [ContinuousSMul ℝ F2] [LocallyConvexSpace ℝ F2]
    (j1 : F1 →L[K] X) (j2 : F2 →L[K] X)
    (hj1 : Function.Injective j1) (hj2 : Function.Injective j2)
    (i : F1 →ₗ[K] F2) (hcompat : ∀ v, j2 (i v) = j1 v) :
    Continuous i := by sorry

end QAlgorithms.Papers.Independent.Intake100.P17

end
