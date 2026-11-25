-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sClosure_isConvexGeometry_of_finiteDimensional
-- name    : PretorsionImageClosed.IndecomposableSkeleton.sClosure_isConvexGeometry_of_finiteDimensional
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:13:30.73191+00:00
-- url     : https://prove2.me/theorems/d09e7a3c-b2f3-5558-a531-e0f446330915
-- title:
--   Indecomposable Skeleton: s Closure is Convex Geometry of finite Dimensional
-- statement:
--   Submodule closure is a convex geometry for the finite-dimensional
--   module setup used in the equidistribution paper.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L311-L318
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L311-L318

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

theorem PretorsionImageClosed.IndecomposableSkeleton.sClosure_isConvexGeometry_of_finiteDimensional
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)] :
    σ.sClosure.IsConvexGeometry := by sorry
