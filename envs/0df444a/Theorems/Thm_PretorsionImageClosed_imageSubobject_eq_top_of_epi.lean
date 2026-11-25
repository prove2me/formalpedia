-- Prove2me | Theorems.Thm_PretorsionImageClosed_imageSubobject_eq_top_of_epi
-- name    : PretorsionImageClosed.imageSubobject_eq_top_of_epi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:14:55.978018+00:00
-- url     : https://prove2.me/theorems/7b73d023-4a19-4eee-ab2c-77c835cd1a99
-- title:
--   Pretorsion Image Closed: image Subobject eq top of epi
-- statement:
--   The image of an epimorphism is everything.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L75-L80
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L75-L80

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

theorem PretorsionImageClosed.imageSubobject_eq_top_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : imageSubobject f = ⊤ := by sorry
