-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P94_bundle_trivializingOpenCover
-- name    : QAlgorithms.Papers.Independent.Intake100.P94.bundle_trivializingOpenCover
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:47:33.026765+00:00
-- url     : https://prove2.me/theorems/e169e807-f35a-4d66-b699-83b856ee088f
-- title:
--   Existence of a trivializing open cover
-- statement:
--   Let $E\to X$ be a $C^r$ vector bundle with Hausdorff locally convex typical fibre $F$, where $r\in\mathbb N_0\cup\{\infty\}$ and $X$ is a Hausdorff, sigma-compact, finite-dimensional $C^r$ manifold. There is an open cover $\mathcal P$ of $X$ such that
--
--   $$
--   \text{for every }P\in\mathcal P,\qquad E|_P\cong P\times F
--   $$
--
--   by a fibrewise linear local $C^r$ trivialization. Neither countability nor local finiteness is imposed on this cover. The assertion supplies the initial trivializing cover for the subsequent chart construction.
-- source:
--   Differentiable mappings between spaces of sections, arXiv:1308.1172v1, PDF p. 16, 5.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P94

namespace QAlgorithms.Papers.Independent.Intake100.P94

open Set Filter Topology Bundle

open QAlgorithms.Papers.Independent.Gap48.P05

universe u v w z

section BundleResults

variable {K : Type u} [RCLike K]

variable {Z : Type v} [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]

variable [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z]

variable [LocallyConvexSpace ℝ Z] [T2Space Z]

variable {X : Type w} [TopologicalSpace X] [T2Space X] [ChartedSpace Z X]

variable {F : Type z} [TopologicalSpace F] [AddCommGroup F]

variable [Module K F] [Module ℝ F] [IsScalarTower ℝ K F]

variable [IsTopologicalAddGroup F] [ContinuousSMul K F] [ContinuousSMul ℝ F]

variable [LocallyConvexSpace ℝ F] [T2Space F]

variable {V : X → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module K (V x)]

variable [∀ x, TopologicalSpace (V x)]

variable [TopologicalSpace (TotalSpace F V)] [T2Space (TotalSpace F V)]

variable [FiberBundle F V]

/-- Numbered assertion 5.2, PDF p. 16: a trivializing open cover.
The finite-dimensional, sigma-compact base assumptions are those of
Section 5.1. The cover is not required to be countable or locally finite;
that stronger refinement is a different assertion (5.3). -/
theorem bundle_trivializingOpenCover
    (r : WithTop ℕ) (B : LCVectorBundle r K Z X F V)
    [FiniteDimensional ℝ Z] [SigmaCompactSpace X] :
    ∃ P : Set (Set X),
      (∀ U ∈ P, IsOpen U) ∧ Set.sUnion P = Set.univ ∧
      ∀ U ∈ P, ∃ e : Trivialization F (Bundle.TotalSpace.proj : TotalSpace F V → X),
        e ∈ trivializationAtlas F V ∧ e.baseSet = U := by sorry

end BundleResults

end QAlgorithms.Papers.Independent.Intake100.P94
