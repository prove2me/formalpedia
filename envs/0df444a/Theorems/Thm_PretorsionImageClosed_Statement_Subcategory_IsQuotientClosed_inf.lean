-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsQuotientClosed_inf
-- name    : PretorsionImageClosed.Statement.Subcategory.IsQuotientClosed.inf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:52:54.308808+00:00
-- url     : https://prove2.me/theorems/e6130c57-af9d-5ca5-855a-1858be788ae3
-- title:
--   Is Quotient Closed: inf
-- statement:
--   The Is Quotient Closed construction uses the inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L204-L206
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L204-L206

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

theorem PretorsionImageClosed.Statement.Subcategory.IsQuotientClosed.inf {Z Z' : Subcategory C} (h : Z.IsQuotientClosed)
    (h' : Z'.IsQuotientClosed) : (Z ⊓ Z').IsQuotientClosed := by sorry
