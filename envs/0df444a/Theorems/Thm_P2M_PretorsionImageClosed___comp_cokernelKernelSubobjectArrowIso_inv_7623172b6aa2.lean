-- Prove2me | Theorems.Thm_P2M_PretorsionImageClosed___comp_cokernelKernelSubobjectArrowIso_inv_7623172b6aa2
-- name    : P2M_PretorsionImageClosed___comp_cokernelKernelSubobjectArrowIso_inv_7623172b6aa2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:58:27.992922+00:00
-- url     : https://prove2.me/theorems/f5b5d648-f382-420f-9228-49d48eaea634
-- title:
--   P2 M Pretorsion Image Closed   comp cokernel Kernel Subobject Arrow Iso inv 7623172b6aa2: P2 M Pretorsion Image Closed   comp cokernel Kernel Subobject Arrow Iso inv 7623172b6aa2
-- statement:
--   The P2 M Pretorsion Image Closed   comp cokernel Kernel Subobject Arrow Iso inv 7623172b6aa2 construction uses the P2 M Pretorsion Image Closed   comp cokernel Kernel Subobject Arrow Iso inv 7623172b6aa2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Quotients.lean#L56-L58
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Quotients.lean#L56-L58

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

theorem P2M_PretorsionImageClosed___comp_cokernelKernelSubobjectArrowIso_inv_7623172b6aa2 {X Q : C} (π : X ⟶ Q) [Epi π] :
    π ≫ (cokernelKernelSubobjectArrowIso π).inv = cokernel.π (kernelSubobject π).arrow := by sorry

alias «PretorsionImageClosed».«π_comp_cokernelKernelSubobjectArrowIso_inv» := P2M_PretorsionImageClosed___comp_cokernelKernelSubobjectArrowIso_inv_7623172b6aa2
