-- Prove2me | Theorems.Thm_PretorsionImageClosed_imageSubobject_comp_iso_hom
-- name    : PretorsionImageClosed.imageSubobject_comp_iso_hom
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:59:47.902082+00:00
-- url     : https://prove2.me/theorems/90f6dab9-47bd-4509-80ea-f3d16ba3e55a
-- title:
--   Pretorsion Image Closed: image Subobject comp iso hom
-- statement:
--   The image of `f ≫ e` for an isomorphism `e` is the transport of the image of `f`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Quotients.lean#L61-L66
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Quotients.lean#L61-L66

module
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Subobjects_Quotients
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C]

theorem PretorsionImageClosed.imageSubobject_comp_iso_hom {X Y Y' : C} (f : X ⟶ Y) (e : Y ≅ Y') :
    imageSubobject (f ≫ e.hom) = Subobject.mk ((imageSubobject f).arrow ≫ e.hom) := by sorry
