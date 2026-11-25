-- Prove2me | Theorems.Thm_PretorsionImageClosed_length_lt_of_mono
-- name    : PretorsionImageClosed.length_lt_of_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:30:37.949364+00:00
-- url     : https://prove2.me/theorems/1685d3ec-b53a-4677-beb5-aacd4ea7c811
-- title:
--   Pretorsion Image Closed: length lt of mono
-- statement:
--   The Pretorsion Image Closed construction uses the length lt of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L60-L61
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L60-L61

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

theorem PretorsionImageClosed.length_lt_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (h : ¬ IsIso f) : length X < length Y := by sorry
