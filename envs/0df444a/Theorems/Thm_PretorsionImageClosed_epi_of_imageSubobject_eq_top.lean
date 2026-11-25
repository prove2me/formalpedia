-- Prove2me | Theorems.Thm_PretorsionImageClosed_epi_of_imageSubobject_eq_top
-- name    : PretorsionImageClosed.epi_of_imageSubobject_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:14:59.52592+00:00
-- url     : https://prove2.me/theorems/c835146e-b39e-4103-9271-f998dc8d734c
-- title:
--   Pretorsion Image Closed: epi of image Subobject eq top
-- statement:
--   A morphism whose image is everything is an epimorphism.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L83-L86
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L83-L86

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

theorem PretorsionImageClosed.epi_of_imageSubobject_eq_top {X Y : C} (f : X ⟶ Y) (h : imageSubobject f = ⊤) : Epi f := by sorry
