-- Prove2me | Theorems.Thm_PretorsionImageClosed_length_eq_of_iso
-- name    : PretorsionImageClosed.length_eq_of_iso
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:30:35.333515+00:00
-- url     : https://prove2.me/theorems/d8a8dc23-2487-4550-9d58-654dae2f0db8
-- title:
--   Pretorsion Image Closed: length eq of iso
-- statement:
--   The Pretorsion Image Closed construction uses the length eq of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L57-L58
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L57-L58

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

theorem PretorsionImageClosed.length_eq_of_iso {X Y : C} (e : X ≅ Y) : length X = length Y := by sorry
