-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_of_isZero_src
-- name    : PretorsionImageClosed.Statement.IsTrivial.of_isZero_src
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:23:54.28178+00:00
-- url     : https://prove2.me/theorems/45bd2075-8fd2-55ee-ab1f-e14a9456aa5f
-- title:
--   Is Trivial: of is Zero src
-- statement:
--   The Is Trivial construction uses the of is Zero src property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L279-L281
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L279-L281

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
open PretorsionImageClosed.Statement

theorem PretorsionImageClosed.Statement.IsTrivial.of_isZero_src {X Y : C} (f : X ⟶ Y) (hX : IsZero X) (Zs : Subcategory C) :
    IsTrivial Zs.prop f := by sorry
