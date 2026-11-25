-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsQuotientClosed_isImageClosed
-- name    : PretorsionImageClosed.Statement.Subcategory.IsQuotientClosed.isImageClosed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:04:31.139591+00:00
-- url     : https://prove2.me/theorems/6e94668f-f21d-4a99-b93d-b1d2d6e304dc
-- title:
--   Is Quotient Closed: is Image Closed
-- statement:
--   The Is Quotient Closed construction uses the is Image Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L239-L241
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L239-L241

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

theorem PretorsionImageClosed.Statement.Subcategory.IsQuotientClosed.isImageClosed {Z : Subcategory A} (h : Z.IsQuotientClosed) :
    Z.IsImageClosed := by sorry
