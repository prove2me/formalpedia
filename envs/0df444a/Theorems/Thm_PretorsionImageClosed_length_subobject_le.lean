-- Prove2me | Theorems.Thm_PretorsionImageClosed_length_subobject_le
-- name    : PretorsionImageClosed.length_subobject_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:12:23.46494+00:00
-- url     : https://prove2.me/theorems/9127ecde-b898-43c1-a3bf-cb8453873e39
-- title:
--   Pretorsion Image Closed: length subobject le
-- statement:
--   The Pretorsion Image Closed construction uses the length subobject le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L92-L92
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L92-L92

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
variable {X : C} (S : Subobject X)

theorem PretorsionImageClosed.length_subobject_le : length (S : C) ≤ length X := by sorry
