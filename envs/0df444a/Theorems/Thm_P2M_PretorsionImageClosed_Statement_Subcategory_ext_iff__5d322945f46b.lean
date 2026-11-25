-- Prove2me | Theorems.Thm_P2M_PretorsionImageClosed_Statement_Subcategory_ext_iff__5d322945f46b
-- name    : P2M_PretorsionImageClosed_Statement_Subcategory_ext_iff__5d322945f46b
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:22:05.840227+00:00
-- url     : https://prove2.me/theorems/995fe92e-613c-59b5-ac66-9edbdc976500
-- title:
--   P2 M Pretorsion Image Closed Statement Subcategory ext iff  5d322945f46b: P2 M Pretorsion Image Closed Statement Subcategory ext iff  5d322945f46b
-- statement:
--   The P2 M Pretorsion Image Closed Statement Subcategory ext iff  5d322945f46b construction uses the P2 M Pretorsion Image Closed Statement Subcategory ext iff  5d322945f46b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L72-L73
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L72-L73

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

theorem P2M_PretorsionImageClosed_Statement_Subcategory_ext_iff__5d322945f46b {Z Z' : Subcategory C} : Z = Z' ↔ ∀ X, Z.prop X ↔ Z'.prop X := by sorry

alias «PretorsionImageClosed».«Statement».«Subcategory».«ext_iff'» := P2M_PretorsionImageClosed_Statement_Subcategory_ext_iff__5d322945f46b
