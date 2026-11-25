-- Prove2me | Theorems.Thm_PretorsionImageClosed_isIso_of_epi_of_length_le
-- name    : PretorsionImageClosed.isIso_of_epi_of_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:19:40.580496+00:00
-- url     : https://prove2.me/theorems/ee37cb39-fa83-445f-a030-806af2d1960d
-- title:
--   Pretorsion Image Closed: is Iso of epi of length le
-- statement:
--   The Pretorsion Image Closed construction uses the is Iso of epi of length le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L81-L84
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L81-L84

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

theorem PretorsionImageClosed.isIso_of_epi_of_length_le {X Y : C} (f : X ⟶ Y) [Epi f] (h : length X ≤ length Y) :
    IsIso f := by sorry
