-- Prove2me | Theorems.Thm_PretorsionImageClosed_kernelSubobject_eq_bot_of_mono
-- name    : PretorsionImageClosed.kernelSubobject_eq_bot_of_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:13:50.248744+00:00
-- url     : https://prove2.me/theorems/5c3fb681-c366-4101-acbf-728722c97428
-- title:
--   Pretorsion Image Closed: kernel Subobject eq bot of mono
-- statement:
--   The Pretorsion Image Closed construction uses the kernel Subobject eq bot of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/SummandReduction.lean#L88-L89
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/SummandReduction.lean#L88-L89

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

theorem PretorsionImageClosed.kernelSubobject_eq_bot_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] : kernelSubobject f = ⊥ := by sorry
