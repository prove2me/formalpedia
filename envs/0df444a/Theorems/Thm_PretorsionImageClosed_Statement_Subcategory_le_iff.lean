-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_iff
-- name    : PretorsionImageClosed.Statement.Subcategory.le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:43:48.294219+00:00
-- url     : https://prove2.me/theorems/3a6f5cd4-f44b-4004-af72-4f8303f07272
-- title:
--   Subcategory: le iff
-- statement:
--   The Subcategory construction uses the le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L115-L115
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L115-L115

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

theorem PretorsionImageClosed.Statement.Subcategory.le_iff {Z Z' : Subcategory C} : Z ≤ Z' ↔ ∀ X, Z.prop X → Z'.prop X := by sorry
