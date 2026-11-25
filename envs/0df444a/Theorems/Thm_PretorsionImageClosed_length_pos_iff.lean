-- Prove2me | Theorems.Thm_PretorsionImageClosed_length_pos_iff
-- name    : PretorsionImageClosed.length_pos_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:09:19.014136+00:00
-- url     : https://prove2.me/theorems/c59d10da-178e-48fe-a72b-4d98841115b5
-- title:
--   Pretorsion Image Closed: length pos iff
-- statement:
--   The Pretorsion Image Closed construction uses the length pos iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L50-L51
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L50-L51

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

theorem PretorsionImageClosed.length_pos_iff (X : C) : 0 < length X ↔ ¬ IsZero X := by sorry
