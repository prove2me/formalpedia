-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_inf_prop_iff
-- name    : PretorsionImageClosed.Statement.Subcategory.inf_prop_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:21:59.983546+00:00
-- url     : https://prove2.me/theorems/227b1fe2-e39f-4c68-933e-f7ad900a78c3
-- title:
--   Subcategory: inf prop iff
-- statement:
--   The Subcategory construction uses the inf prop iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L157-L158
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L157-L158

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

theorem PretorsionImageClosed.Statement.Subcategory.inf_prop_iff (Z Z' : Subcategory C) (X : C) :
    (Z ⊓ Z').prop X ↔ Z.prop X ∧ Z'.prop X := by sorry
