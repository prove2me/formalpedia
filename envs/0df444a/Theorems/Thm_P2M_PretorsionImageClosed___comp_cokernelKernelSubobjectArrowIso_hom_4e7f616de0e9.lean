-- Prove2me | Theorems.Thm_P2M_PretorsionImageClosed___comp_cokernelKernelSubobjectArrowIso_hom_4e7f616de0e9
-- name    : P2M_PretorsionImageClosed___comp_cokernelKernelSubobjectArrowIso_hom_4e7f616de0e9
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:58:08.051912+00:00
-- url     : https://prove2.me/theorems/d01ddf23-a688-5428-bc02-051d2175f445
-- title:
--   P2 M Pretorsion Image Closed   comp cokernel Kernel Subobject Arrow Iso hom 4e7f616de0e9: P2 M Pretorsion Image Closed   comp cokernel Kernel Subobject Arrow Iso hom 4e7f616de0e9
-- statement:
--   The P2 M Pretorsion Image Closed   comp cokernel Kernel Subobject Arrow Iso hom 4e7f616de0e9 construction uses the P2 M Pretorsion Image Closed   comp cokernel Kernel Subobject Arrow Iso hom 4e7f616de0e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Quotients.lean#L52-L54
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Quotients.lean#L52-L54

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

theorem P2M_PretorsionImageClosed___comp_cokernelKernelSubobjectArrowIso_hom_4e7f616de0e9 {X Q : C} (π : X ⟶ Q) [Epi π] :
    cokernel.π (kernelSubobject π).arrow ≫ (cokernelKernelSubobjectArrowIso π).hom = π := by sorry

alias «PretorsionImageClosed».«π_comp_cokernelKernelSubobjectArrowIso_hom» := P2M_PretorsionImageClosed___comp_cokernelKernelSubobjectArrowIso_hom_4e7f616de0e9
