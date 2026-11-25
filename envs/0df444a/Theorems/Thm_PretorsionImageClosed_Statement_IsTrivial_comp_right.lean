-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_comp_right
-- name    : PretorsionImageClosed.Statement.IsTrivial.comp_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:52:56.364806+00:00
-- url     : https://prove2.me/theorems/7b106087-4a9e-4aec-93f2-d5f28d0ef9ee
-- title:
--   Is Trivial: comp right
-- statement:
--   The Is Trivial construction uses the comp right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L48-L51
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L48-L51

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

theorem PretorsionImageClosed.Statement.IsTrivial.comp_right {X Y W : C} {f : X ⟶ Y} (h : IsTrivial Z f) (g : Y ⟶ W) :
    IsTrivial Z (f ≫ g) := by sorry
