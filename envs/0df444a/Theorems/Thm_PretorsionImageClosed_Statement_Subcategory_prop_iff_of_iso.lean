-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_iff_of_iso
-- name    : PretorsionImageClosed.Statement.Subcategory.prop_iff_of_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:53:55.10506+00:00
-- url     : https://prove2.me/theorems/c1d92628-3563-42ed-828a-ddd4a8caee81
-- title:
--   Subcategory: prop iff of iso
-- statement:
--   The Subcategory construction uses the prop iff of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L78-L79
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L78-L79

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

theorem PretorsionImageClosed.Statement.Subcategory.prop_iff_of_iso {X Y : C} (e : X ≅ Y) : Z.prop X ↔ Z.prop Y := by sorry
