-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_of_prop_src
-- name    : PretorsionImageClosed.Statement.IsTrivial.of_prop_src
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:16:46.19745+00:00
-- url     : https://prove2.me/theorems/7dc584a8-d5ac-4dbe-b90e-86c9e4daf0d5
-- title:
--   Is Trivial: of prop src
-- statement:
--   The Is Trivial construction uses the of prop src property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L37-L38
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L37-L38

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

theorem PretorsionImageClosed.Statement.IsTrivial.of_prop_src {X Y : C} (f : X ⟶ Y) (hX : Z X) : IsTrivial Z f := by sorry
