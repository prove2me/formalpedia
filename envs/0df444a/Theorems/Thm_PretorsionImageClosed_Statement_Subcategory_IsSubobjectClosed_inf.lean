-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsSubobjectClosed_inf
-- name    : PretorsionImageClosed.Statement.Subcategory.IsSubobjectClosed.inf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:53:05.053639+00:00
-- url     : https://prove2.me/theorems/a9877c16-8826-5eb1-9869-60e606f41618
-- title:
--   Is Subobject Closed: inf
-- statement:
--   The Is Subobject Closed construction uses the inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L208-L210
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L208-L210

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
open PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
variable (Z : Subcategory C)

theorem PretorsionImageClosed.Statement.Subcategory.IsSubobjectClosed.inf {Z Z' : Subcategory C} (h : Z.IsSubobjectClosed)
    (h' : Z'.IsSubobjectClosed) : (Z ⊓ Z').IsSubobjectClosed := by sorry
