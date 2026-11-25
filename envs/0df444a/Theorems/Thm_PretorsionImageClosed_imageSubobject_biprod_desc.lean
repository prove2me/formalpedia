-- Prove2me | Theorems.Thm_PretorsionImageClosed_imageSubobject_biprod_desc
-- name    : PretorsionImageClosed.imageSubobject_biprod_desc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:12:33.644932+00:00
-- url     : https://prove2.me/theorems/f9f9151a-29fe-561c-b77f-d649af94cf3f
-- title:
--   Pretorsion Image Closed: image Subobject biprod desc
-- statement:
--   The image of `biprod.desc f g` is the sum of the images of `f` and `g`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/SummandReduction.lean#L51-L59
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/SummandReduction.lean#L51-L59

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
variable {C : Type*} [Category C] [Abelian C]

theorem PretorsionImageClosed.imageSubobject_biprod_desc {Y₁ Y₂ X : C} (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) :
    imageSubobject (biprod.desc f g) = sumSubobject (imageSubobject f) (imageSubobject g) := by sorry
