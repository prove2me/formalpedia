-- Prove2me | Theorems.Thm_PretorsionImageClosed_Subobject_kernelSubobject_le_preimage
-- name    : PretorsionImageClosed.Subobject.kernelSubobject_le_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:46:17.489394+00:00
-- url     : https://prove2.me/theorems/cb519195-50f7-400e-877b-562acba13ebb
-- title:
--   Subobject: kernel Subobject le preimage
-- statement:
--   The Subobject construction uses the kernel Subobject le preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L145-L148
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L145-L148

module
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C]

theorem PretorsionImageClosed.Subobject.kernelSubobject_le_preimage {X Y : C} (p : X ⟶ Y) (U : Subobject Y) :
    kernelSubobject p ≤ Subobject.preimage p U := by sorry
