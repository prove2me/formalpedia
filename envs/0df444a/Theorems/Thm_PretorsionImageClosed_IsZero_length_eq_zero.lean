-- Prove2me | Theorems.Thm_PretorsionImageClosed_IsZero_length_eq_zero
-- name    : PretorsionImageClosed.IsZero.length_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:18:59.080325+00:00
-- url     : https://prove2.me/theorems/654999f2-8c29-5dd3-a826-567f86f0b709
-- title:
--   Is Zero: length eq zero
-- statement:
--   The Is Zero construction uses the length eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L53-L53
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L53-L53

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

theorem PretorsionImageClosed.IsZero.length_eq_zero {X : C} (h : IsZero X) : length X = 0 := by sorry
