-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsImageClosed_inf_of_closed
-- name    : PretorsionImageClosed.Statement.Subcategory.IsImageClosed.inf_of_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:54:21.359983+00:00
-- url     : https://prove2.me/theorems/303ecc10-777a-47d4-b119-a655138fbe88
-- title:
--   Is Image Closed: inf of closed
-- statement:
--   Equation (2.1): the intersection of a quotient-closed and a subobject-closed
--   subcategory is image-closed.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L249-L251
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L249-L251

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

theorem PretorsionImageClosed.Statement.Subcategory.IsImageClosed.inf_of_closed {T F : Subcategory A} (hT : T.IsQuotientClosed)
    (hF : F.IsSubobjectClosed) : (T ⊓ F).IsImageClosed := by sorry
