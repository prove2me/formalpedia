-- Prove2me | Theorems.Thm_PretorsionImageClosed_mono_of_kernelSubobject_eq_bot
-- name    : PretorsionImageClosed.mono_of_kernelSubobject_eq_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:13:42.375031+00:00
-- url     : https://prove2.me/theorems/976f7ea8-4a61-4ff6-b4f2-011f433651f4
-- title:
--   Pretorsion Image Closed: mono of kernel Subobject eq bot
-- statement:
--   The Pretorsion Image Closed construction uses the mono of kernel Subobject eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/SummandReduction.lean#L85-L86
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/SummandReduction.lean#L85-L86

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

theorem PretorsionImageClosed.mono_of_kernelSubobject_eq_bot {X Y : C} (f : X ⟶ Y) (h : kernelSubobject f = ⊥) : Mono f := by sorry
