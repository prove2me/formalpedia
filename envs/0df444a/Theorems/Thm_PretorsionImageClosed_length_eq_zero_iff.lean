-- Prove2me | Theorems.Thm_PretorsionImageClosed_length_eq_zero_iff
-- name    : PretorsionImageClosed.length_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:30:33.445022+00:00
-- url     : https://prove2.me/theorems/fca9b148-2846-4b45-9698-48c76d465f50
-- title:
--   Pretorsion Image Closed: length eq zero iff
-- statement:
--   The Pretorsion Image Closed construction uses the length eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L48-L48
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L48-L48

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

theorem PretorsionImageClosed.length_eq_zero_iff (X : C) : length X = 0 ↔ IsZero X := by sorry
