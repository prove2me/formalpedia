-- Prove2me | Theorems.Thm_PretorsionImageClosed_kernelSubobject_biprod_lift
-- name    : PretorsionImageClosed.kernelSubobject_biprod_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:13:43.66265+00:00
-- url     : https://prove2.me/theorems/38372618-46d1-4b1a-abc8-eab288f36c79
-- title:
--   Pretorsion Image Closed: kernel Subobject biprod lift
-- statement:
--   The kernel of `biprod.lift f g` is the intersection of the kernels.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/SummandReduction.lean#L62-L83
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/SummandReduction.lean#L62-L83

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

theorem PretorsionImageClosed.kernelSubobject_biprod_lift {X Y₁ Y₂ : C} (f : X ⟶ Y₁) (g : X ⟶ Y₂) :
    kernelSubobject (biprod.lift f g) = kernelSubobject f ⊓ kernelSubobject g := by sorry
