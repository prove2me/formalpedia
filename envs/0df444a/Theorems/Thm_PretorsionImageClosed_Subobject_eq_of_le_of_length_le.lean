-- Prove2me | Theorems.Thm_PretorsionImageClosed_Subobject_eq_of_le_of_length_le
-- name    : PretorsionImageClosed.Subobject.eq_of_le_of_length_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:57:26.865+00:00
-- url     : https://prove2.me/theorems/459a80c4-62d0-4918-aeb2-7db447dd3064
-- title:
--   Subobject: eq of le of length le
-- statement:
--   Two nested subobjects of the same length coincide.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L98-L102
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L98-L102

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

theorem PretorsionImageClosed.Subobject.eq_of_le_of_length_le {S T : Subobject X} (h : S ≤ T)
    (hl : length (T : C) ≤ length (S : C)) : S = T := by sorry
