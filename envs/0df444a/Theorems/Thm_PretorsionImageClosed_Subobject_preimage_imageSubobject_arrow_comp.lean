-- Prove2me | Theorems.Thm_PretorsionImageClosed_Subobject_preimage_imageSubobject_arrow_comp
-- name    : PretorsionImageClosed.Subobject.preimage_imageSubobject_arrow_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:15:05.633992+00:00
-- url     : https://prove2.me/theorems/e3581f7e-7828-45c8-b53b-8589f874d73e
-- title:
--   Subobject: preimage image Subobject arrow comp
-- statement:
--   For an epimorphism `p` and a subobject `S` containing `ker p`, the preimage
--   of the image of `S` is `S`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L185-L203
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L185-L203

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

theorem PretorsionImageClosed.Subobject.preimage_imageSubobject_arrow_comp {X Y : C} (p : X ⟶ Y) [Epi p]
    (S : Subobject X) (hS : kernelSubobject p ≤ S) :
    Subobject.preimage p (imageSubobject (S.arrow ≫ p)) = S := by sorry
