-- Prove2me | Theorems.Thm_PretorsionImageClosed_Subobject_lt_length_of_lt
-- name    : PretorsionImageClosed.Subobject.lt_length_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:19:55.928379+00:00
-- url     : https://prove2.me/theorems/56402eab-4861-45db-8609-b2f21050e757
-- title:
--   Subobject: lt length of lt
-- statement:
--   The Subobject construction uses the lt length of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L104-L107
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L104-L107

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

theorem PretorsionImageClosed.Subobject.lt_length_of_lt {S T : Subobject X} (h : S < T) :
    length (S : C) < length (T : C) := by sorry
