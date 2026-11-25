-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_union
-- name    : PretorsionImageClosed.IndecomposableSkeleton.reject_union
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:13:39.074262+00:00
-- url     : https://prove2.me/theorems/40f2699a-0bc5-42e7-894c-799fe83f04af
-- title:
--   Indecomposable Skeleton: reject union
-- statement:
--   Reject converts unions of selected indecomposables to meets.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L131-L180
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L131-L180

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

theorem PretorsionImageClosed.IndecomposableSkeleton.reject_union (S T : Set ι) (X : FGModuleCat.{w} R) :
    σ.reject (S ∪ T) X = σ.reject S X ⊓ σ.reject T X := by sorry
