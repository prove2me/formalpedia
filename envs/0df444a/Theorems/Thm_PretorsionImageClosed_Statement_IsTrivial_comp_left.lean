-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_comp_left
-- name    : PretorsionImageClosed.Statement.IsTrivial.comp_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:38:16.571333+00:00
-- url     : https://prove2.me/theorems/a412549c-3773-45b6-af93-176977fb48fd
-- title:
--   Is Trivial: comp left
-- statement:
--   The Is Trivial construction uses the comp left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L43-L46
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L43-L46

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

theorem PretorsionImageClosed.Statement.IsTrivial.comp_left {X Y W : C} {f : X ⟶ Y} (h : IsTrivial Z f) (g : W ⟶ X) :
    IsTrivial Z (g ≫ f) := by sorry
