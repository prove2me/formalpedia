-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_def
-- name    : PretorsionImageClosed.Statement.Subcategory.le_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:38:10.816229+00:00
-- url     : https://prove2.me/theorems/93ff6574-63d2-455e-b32d-2ab4c0c23b02
-- title:
--   Subcategory: le def
-- statement:
--   The Subcategory construction uses the le def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L113-L113
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L113-L113

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

theorem PretorsionImageClosed.Statement.Subcategory.le_def {Z Z' : Subcategory C} : Z ≤ Z' ↔ Z.prop ≤ Z'.prop := by sorry
