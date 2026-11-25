-- Prove2me | Theorems.Thm_PretorsionImageClosed_Subobject_underlyingIso_inv_comp_push_arrow
-- name    : PretorsionImageClosed.Subobject.underlyingIso_inv_comp_push_arrow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:16:39.824211+00:00
-- url     : https://prove2.me/theorems/9504310d-f468-43b9-aa7a-9371b3c56214
-- title:
--   Subobject: underlying Iso inv comp push arrow
-- statement:
--   The Subobject construction uses the underlying Iso inv comp push arrow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L220-L223
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L220-L223

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

theorem PretorsionImageClosed.Subobject.underlyingIso_inv_comp_push_arrow :
    (Subobject.underlyingIso (K.arrow ≫ S.arrow)).inv ≫ (Subobject.push S K).arrow =
      K.arrow ≫ S.arrow := by sorry
