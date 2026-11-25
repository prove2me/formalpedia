-- Prove2me | Theorems.Thm_PretorsionImageClosed_Subobject_preimage_factors_iff
-- name    : PretorsionImageClosed.Subobject.preimage_factors_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:15:12.478967+00:00
-- url     : https://prove2.me/theorems/58594e4e-079c-4f35-ade3-86b2a11d7158
-- title:
--   Subobject: preimage factors iff
-- statement:
--   The Subobject construction uses the preimage factors iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L121-L124
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L121-L124

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

theorem PretorsionImageClosed.Subobject.preimage_factors_iff {X Y W : C} (p : X ⟶ Y) (U : Subobject Y) (f : W ⟶ X) :
    (Subobject.preimage p U).Factors f ↔ U.Factors (f ≫ p) := by sorry
