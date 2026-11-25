-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_indOf_addOf
-- name    : PretorsionImageClosed.IndecomposableSkeleton.indOf_addOf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T06:07:00.061631+00:00
-- url     : https://prove2.me/theorems/01bcf0b4-6e3b-52b4-b778-d5edb7439f15
-- title:
--   Indecomposable Skeleton: ind Of add Of
-- statement:
--   The Indecomposable Skeleton construction uses the ind Of add Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Subcategories.lean#L152-L154
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Subcategories.lean#L152-L154

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

theorem PretorsionImageClosed.IndecomposableSkeleton.indOf_addOf (S : Set ι) : σ.indOf (σ.addOf S) = S := by sorry
