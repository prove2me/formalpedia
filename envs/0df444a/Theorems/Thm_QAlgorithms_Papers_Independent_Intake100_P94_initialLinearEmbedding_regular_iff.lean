-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P94_initialLinearEmbedding_regular_iff
-- name    : QAlgorithms.Papers.Independent.Intake100.P94.initialLinearEmbedding_regular_iff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:45:56.286878+00:00
-- url     : https://prove2.me/theorems/5e5496c3-5ba1-4140-8b3b-9393379cd1fd
-- title:
--   Regularity detected by an initial linear embedding
-- statement:
--   Let $E,F$ and $(F_i)_{i\in I}$ be Hausdorff locally convex spaces over $\mathbb K\in\{\mathbb R,\mathbb C\}$, let $U\subseteq E$ be open, and let $r\in\mathbb N_0\cup\{\infty\}$. Suppose the continuous linear maps $\rho_i:F\to F_i$ induce the topology of $F$, and their combined map $\rho:F\to\prod_{i\in I}F_i$ is injective with sequentially closed image. For every map $f:U\to F$,
--
--   $$
--   f\text{ is }C^r\quad\Longleftrightarrow\quad
--   \rho_i\circ f\text{ is }C^r\text{ for every }i\in I.
--   $$
--
--   Here differentiability is the Michal–Bastiani calculus on underlying real spaces. The index set is arbitrary; completeness and closedness of the image are not assumed. This criterion detects differentiability through linear coordinates.
--
--   **Formalization Note** A map on $U$ is represented by any extension to $E$. All regularity conditions are restricted to $U$.
-- source:
--   Differentiable mappings between spaces of sections, arXiv:1308.1172v1, PDF p. 5, 1.9

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P94

namespace QAlgorithms.Papers.Independent.Intake100.P94

open Set Filter Topology Bundle

open QAlgorithms.Papers.Independent.Gap48.P05

universe u v w z

/-- Proposition 1.9, PDF p. 5. Initial topology and injectivity are
encoded together by IsEmbedding of the product of the continuous linear
maps. Its image is only assumed sequentially closed, and I is arbitrary.
A map on U is represented by an arbitrary extension f to E; all regularity
conditions are on U and are independent of that extension. -/
theorem initialLinearEmbedding_regular_iff
    {K : Type u} [RCLike K]
    {E : Type v} [TopologicalSpace E] [AddCommGroup E]
    [Module K E] [Module ℝ E] [IsScalarTower ℝ K E]
    [IsTopologicalAddGroup E] [ContinuousSMul K E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E]
    {F : Type w} [TopologicalSpace F] [AddCommGroup F]
    [Module K F] [Module ℝ F] [IsScalarTower ℝ K F]
    [IsTopologicalAddGroup F] [ContinuousSMul K F] [ContinuousSMul ℝ F]
    [LocallyConvexSpace ℝ F] [T2Space F]
    {I : Type*} {Fi : I → Type z}
    [∀ i, TopologicalSpace (Fi i)] [∀ i, AddCommGroup (Fi i)]
    [∀ i, Module K (Fi i)] [∀ i, Module ℝ (Fi i)]
    [∀ i, IsScalarTower ℝ K (Fi i)]
    [∀ i, IsTopologicalAddGroup (Fi i)]
    [∀ i, ContinuousSMul K (Fi i)] [∀ i, ContinuousSMul ℝ (Fi i)]
    [∀ i, LocallyConvexSpace ℝ (Fi i)] [∀ i, T2Space (Fi i)]
    (r : WithTop ℕ) (U : Set E) (hU : IsOpen U) (f : E → F)
    (rho : ∀ i, F →L[K] Fi i)
    (hEmbedding : Topology.IsEmbedding (fun y : F => fun i => rho i y))
    (hSequential : IsSeqClosed (Set.range (fun y : F => fun i => rho i y))) :
    MBOrder r U f ↔ ∀ i, MBOrder r U (fun x => rho i (f x)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P94
