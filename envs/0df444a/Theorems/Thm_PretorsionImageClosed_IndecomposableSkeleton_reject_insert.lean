-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_insert
-- name    : PretorsionImageClosed.IndecomposableSkeleton.reject_insert
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:13:54.153914+00:00
-- url     : https://prove2.me/theorems/1990952c-4fa7-4e93-a931-01ff66cc30fc
-- title:
--   Indecomposable Skeleton: reject insert
-- statement:
--   Adjoining one indecomposable intersects with its point reject.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L183-L188
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L183-L188

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

theorem PretorsionImageClosed.IndecomposableSkeleton.reject_insert (S : Set ι) (i : ι)
    (X : FGModuleCat.{w} R) :
    σ.reject (insert i S) X =
      σ.reject S X ⊓ σ.pointReject i X := by sorry
