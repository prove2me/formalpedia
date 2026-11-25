-- Prove2me | Theorems.Thm_PretorsionImageClosed_imageSubobject_epi_comp
-- name    : PretorsionImageClosed.imageSubobject_epi_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:00:53.211638+00:00
-- url     : https://prove2.me/theorems/d1eb8357-fd89-4054-8b07-779cf5a086eb
-- title:
--   Pretorsion Image Closed: image Subobject epi comp
-- statement:
--   Precomposing with an epimorphism does not change the image.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L66-L72
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L66-L72

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

theorem PretorsionImageClosed.imageSubobject_epi_comp {W X Y : C} (e : W ⟶ X) [Epi e] (f : X ⟶ Y) :
    imageSubobject (e ≫ f) = imageSubobject f := by sorry
