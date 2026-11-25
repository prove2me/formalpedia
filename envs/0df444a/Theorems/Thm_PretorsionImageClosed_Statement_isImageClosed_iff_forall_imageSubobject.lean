-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isImageClosed_iff_forall_imageSubobject
-- name    : PretorsionImageClosed.Statement.isImageClosed_iff_forall_imageSubobject
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:06:49.394662+00:00
-- url     : https://prove2.me/theorems/66f4429e-04e5-49ee-9d7e-7016631c2e2c
-- title:
--   Statement: is Image Closed iff forall image Subobject
-- statement:
--   The Statement construction uses the is Image Closed iff forall image Subobject property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/TheoremA.lean#L43-L46
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/TheoremA.lean#L43-L46

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits ZeroObject
open PretorsionImageClosed.Statement
open Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]

theorem PretorsionImageClosed.Statement.isImageClosed_iff_forall_imageSubobject (Z : Subcategory C) :
    Z.IsImageClosed ↔ ∀ {X N : C} (f : X ⟶ N), Z.prop X → Z.prop N → Z.prop (imageSubobject f : C) := by sorry
