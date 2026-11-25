-- Prove2me | Theorems.Thm_PretorsionImageClosed_length_le_of_epi
-- name    : PretorsionImageClosed.length_le_of_epi
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:19:15.257265+00:00
-- url     : https://prove2.me/theorems/26ba1ebc-3b2c-558c-83aa-15005e6f6cf9
-- title:
--   Pretorsion Image Closed: length le of epi
-- statement:
--   The Pretorsion Image Closed construction uses the length le of epi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L71-L74
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L71-L74

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

theorem PretorsionImageClosed.length_le_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : length Y ≤ length X := by sorry
