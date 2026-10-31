-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P94_whitneyDomain_isOpen
-- name    : QAlgorithms.Papers.Independent.Intake100.P94.whitneyDomain_isOpen
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:46:50.474777+00:00
-- url     : https://prove2.me/theorems/8c22df09-5dad-48b1-8970-fc40c8257ad9
-- title:
--   Openness of a fibrewise product domain
-- statement:
--   Let $E_1\to X$ and $E_2\to X$ be $C^r$ vector bundles with Hausdorff locally convex fibres over the same Hausdorff $C^r$ manifold, where $r\in\mathbb N_0\cup\{\infty\}$. For an open subset $U\subseteq E_1$, define
--
--   $$
--   U\oplus E_2=\bigcup_{x\in X}(U\cap(E_1)_x)\times(E_2)_x.
--   $$
--
--   Then $U\oplus E_2$ is open in the Whitney sum $E_1\oplus E_2$. The Whitney sum has its natural topology, equivalently the subspace topology on pairs of vectors with the same base point. No finite-dimensionality, sigma-compactness, or zero-section containment is required. This gives the open domains used for vertical differentiation.
-- source:
--   Differentiable mappings between spaces of sections, arXiv:1308.1172v1, PDF p. 12, 3.13

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

variable {F2 : Type*} [TopologicalSpace F2] [AddCommGroup F2]

variable [Module K F2] [Module ℝ F2] [IsScalarTower ℝ K F2]

variable [IsTopologicalAddGroup F2] [ContinuousSMul K F2] [ContinuousSMul ℝ F2]

variable [LocallyConvexSpace ℝ F2] [T2Space F2]

variable {V2 : X → Type*} [∀ x, AddCommGroup (V2 x)] [∀ x, Module K (V2 x)]

variable [∀ x, TopologicalSpace (V2 x)]

variable [TopologicalSpace (TotalSpace F2 V2)] [T2Space (TotalSpace F2 V2)]

variable [FiberBundle F2 V2]

/-- Numbered assertion 3.13, PDF p. 12: the concrete fibrewise union
U plus E2 is open in the Whitney sum. The base and fibres may have
arbitrary dimension; no sigma-compactness or zero-section condition on
U is used in this assertion. -/
theorem whitneyDomain_isOpen
    (r : WithTop ℕ) (B1 : LCVectorBundle r K Z X F V)
    (B2 : LCVectorBundle r K Z X F2 V2)
    (U : Set (TotalSpace F V)) (hU : IsOpen U) :
    IsOpen (OpenWhitneyDomain (F2 := F2) (V2 := V2) U) := by sorry

end BundleResults

end QAlgorithms.Papers.Independent.Intake100.P94
