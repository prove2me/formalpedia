-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_addOf_prop
-- name    : PretorsionImageClosed.IndecomposableSkeleton.addOf_prop
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T06:54:36.053002+00:00
-- url     : https://prove2.me/theorems/890eeb6c-ac71-45f9-8c9b-dab0501219fe
-- title:
--   Indecomposable Skeleton: add Of prop
-- statement:
--   The Indecomposable Skeleton construction uses the add Of prop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Subcategories.lean#L143-L144
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Subcategories.lean#L143-L144

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitInjective
public import Definitions.Def_PretorsionImageClosed_Subcategories_Biproducts
public import Definitions.Def_PretorsionImageClosed_Statement
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R] {ι : Type v}
  (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

theorem PretorsionImageClosed.IndecomposableSkeleton.addOf_prop {S : Set ι} {X : FGModuleCat.{w} R} : (σ.addOf S).prop X ↔ σ.InAdd S X := by sorry
