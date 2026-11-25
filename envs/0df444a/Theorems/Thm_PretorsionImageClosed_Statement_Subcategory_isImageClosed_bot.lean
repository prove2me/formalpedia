-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_isImageClosed_bot
-- name    : PretorsionImageClosed.Statement.Subcategory.isImageClosed_bot
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:23:01.411809+00:00
-- url     : https://prove2.me/theorems/7f0633c1-b2a1-536b-b33d-c4848c193333
-- title:
--   Subcategory: is Image Closed bot
-- statement:
--   The Subcategory construction uses the is Image Closed bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L264-L265
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L264-L265

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement ZeroObject
variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
variable {A : Type*} [Category A] [Abelian A]
open PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
variable (Z : Subcategory A)

theorem PretorsionImageClosed.Statement.Subcategory.isImageClosed_bot : (⊥ : Subcategory A).IsImageClosed := by sorry
