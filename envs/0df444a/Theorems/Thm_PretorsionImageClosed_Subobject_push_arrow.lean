-- Prove2me | Theorems.Thm_PretorsionImageClosed_Subobject_push_arrow
-- name    : PretorsionImageClosed.Subobject.push_arrow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:52:50.771363+00:00
-- url     : https://prove2.me/theorems/874309b7-2cbd-4667-8d57-b10b1bdad4ed
-- title:
--   Subobject: push arrow
-- statement:
--   The Subobject construction uses the push arrow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L225-L227
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L225-L227

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
variable {C : Type*} [Category C] [Abelian C] {X : C} (S : Subobject X) (K : Subobject (S : C))

theorem PretorsionImageClosed.Subobject.push_arrow :
    (Subobject.push S K).arrow = (Subobject.underlyingIso (K.arrow ≫ S.arrow)).hom ≫ K.arrow ≫ S.arrow := by sorry
