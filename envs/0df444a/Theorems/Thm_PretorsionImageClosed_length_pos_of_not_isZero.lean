-- Prove2me | Theorems.Thm_PretorsionImageClosed_length_pos_of_not_isZero
-- name    : PretorsionImageClosed.length_pos_of_not_isZero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:19:25.49082+00:00
-- url     : https://prove2.me/theorems/06720c3b-bb0c-4305-8579-d9189aafa2b0
-- title:
--   Pretorsion Image Closed: length pos of not is Zero
-- statement:
--   The Pretorsion Image Closed construction uses the length pos of not is Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L55-L55
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L55-L55

module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Definitions.Def_PretorsionImageClosed_Length_Basic
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasLength C]

theorem PretorsionImageClosed.length_pos_of_not_isZero {X : C} (h : ¬ IsZero X) : 0 < length X := by sorry
