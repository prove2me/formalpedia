-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsImageClosed_inf
-- name    : PretorsionImageClosed.Statement.Subcategory.IsImageClosed.inf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:55:58.590807+00:00
-- url     : https://prove2.me/theorems/3f4558e2-a8e4-41e8-bd11-aa3748d7d21f
-- title:
--   Is Image Closed: inf
-- statement:
--   The Is Image Closed construction uses the inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L253-L254
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L253-L254

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
variable {A : Type*} [Category A] [Abelian A]
open PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
variable (Z : Subcategory A)

theorem PretorsionImageClosed.Statement.Subcategory.IsImageClosed.inf {Z Z' : Subcategory A} (h : Z.IsImageClosed) (h' : Z'.IsImageClosed) :
    (Z ⊓ Z').IsImageClosed := by sorry
