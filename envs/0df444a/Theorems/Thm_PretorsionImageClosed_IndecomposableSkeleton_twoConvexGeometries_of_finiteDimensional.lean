-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_twoConvexGeometries_of_finiteDimensional
-- name    : PretorsionImageClosed.IndecomposableSkeleton.twoConvexGeometries_of_finiteDimensional
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:15:45.101187+00:00
-- url     : https://prove2.me/theorems/eeb675df-b2a8-5ec7-908c-dbc8d9b3a1d5
-- title:
--   Indecomposable Skeleton: two Convex Geometries of finite Dimensional
-- statement:
--   In finite representation type, quotient and submodule closure give
--   the two finite convex geometries asserted in the equidistribution paper.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L336-L345
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L336-L345

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

theorem PretorsionImageClosed.IndecomposableSkeleton.twoConvexGeometries_of_finiteDimensional
    [Finite ι]
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)] :
    σ.qClosure.IsConvexGeometry ∧
      σ.sClosure.IsConvexGeometry := by sorry
