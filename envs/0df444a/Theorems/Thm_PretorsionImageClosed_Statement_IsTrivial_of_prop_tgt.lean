-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_of_prop_tgt
-- name    : PretorsionImageClosed.Statement.IsTrivial.of_prop_tgt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:20:39.108558+00:00
-- url     : https://prove2.me/theorems/65b28e28-d4e0-5ef3-9e61-f91c1b71fbec
-- title:
--   Is Trivial: of prop tgt
-- statement:
--   The Is Trivial construction uses the of prop tgt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L40-L41
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L40-L41

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
open PretorsionImageClosed.Statement
variable {C : Type*} [Category C] {Z : ObjectProperty C}

theorem PretorsionImageClosed.Statement.IsTrivial.of_prop_tgt {X Y : C} (f : X ⟶ Y) (hY : Z Y) : IsTrivial Z f := by sorry
