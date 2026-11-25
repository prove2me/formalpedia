-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qClosure_isConvexGeometry
-- name    : PretorsionImageClosed.IndecomposableSkeleton.qClosure_isConvexGeometry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:15:06.652146+00:00
-- url     : https://prove2.me/theorems/46283184-92bc-5b1b-8912-86c87a282743
-- title:
--   Indecomposable Skeleton: q Closure is Convex Geometry
-- statement:
--   Under the Artinian endomorphism-ring hypothesis, quotient closure is
--   a convex geometry.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/QuotientAntiExchange.lean#L221-L224
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/QuotientAntiExchange.lean#L221-L224

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
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

theorem PretorsionImageClosed.IndecomposableSkeleton.qClosure_isConvexGeometry
    [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))] :
    σ.qClosure.IsConvexGeometry := by sorry
