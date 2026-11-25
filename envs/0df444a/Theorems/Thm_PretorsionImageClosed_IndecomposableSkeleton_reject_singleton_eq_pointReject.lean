-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_singleton_eq_pointReject
-- name    : PretorsionImageClosed.IndecomposableSkeleton.reject_singleton_eq_pointReject
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:13:25.711646+00:00
-- url     : https://prove2.me/theorems/35c8ad23-ca52-4e70-b640-e7253df406f6
-- title:
--   Indecomposable Skeleton: reject singleton eq point Reject
-- statement:
--   The reject against a singleton is the common kernel of all maps to
--   that indecomposable.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L64-L128
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L64-L128

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

theorem PretorsionImageClosed.IndecomposableSkeleton.reject_singleton_eq_pointReject (i : ι)
    (X : FGModuleCat.{w} R) :
    σ.reject {i} X = σ.pointReject i X := by sorry
