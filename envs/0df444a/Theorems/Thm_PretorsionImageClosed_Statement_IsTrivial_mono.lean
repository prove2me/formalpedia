-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_mono
-- name    : PretorsionImageClosed.Statement.IsTrivial.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:38:12.802466+00:00
-- url     : https://prove2.me/theorems/220a4a16-0486-4886-8c1f-626a002b3849
-- title:
--   Is Trivial: mono
-- statement:
--   The Is Trivial construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L53-L56
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L53-L56

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

theorem PretorsionImageClosed.Statement.IsTrivial.mono {Z' : ObjectProperty C} (hZ : Z ≤ Z') {X Y : C} {f : X ⟶ Y}
    (h : IsTrivial Z f) : IsTrivial Z' f := by sorry
