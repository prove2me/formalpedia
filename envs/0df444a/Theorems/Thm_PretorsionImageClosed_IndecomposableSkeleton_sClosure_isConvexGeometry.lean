-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sClosure_isConvexGeometry
-- name    : PretorsionImageClosed.IndecomposableSkeleton.sClosure_isConvexGeometry
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:15:13.516475+00:00
-- url     : https://prove2.me/theorems/2fed995c-b295-5a3f-87ed-8bec80eeffa5
-- title:
--   Indecomposable Skeleton: s Closure is Convex Geometry
-- statement:
--   Under the Artinian endomorphism-ring hypothesis, submodule closure
--   is a convex geometry.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L289-L292
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L289-L292

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

theorem PretorsionImageClosed.IndecomposableSkeleton.sClosure_isConvexGeometry
    [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))] :
    σ.sClosure.IsConvexGeometry := by sorry
