-- Prove2me | Theorems.Thm_PretorsionImageClosed_idealRange_top
-- name    : PretorsionImageClosed.idealRange_top
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:05:43.936525+00:00
-- url     : https://prove2.me/theorems/be514f1f-cf07-5b25-b2a1-736794b4f803
-- title:
--   Pretorsion Image Closed: ideal Range top
-- statement:
--   The Pretorsion Image Closed construction uses the ideal Range top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L218-L226
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L218-L226

module
public import Mathlib.RingTheory.Artinian.Ring
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Function
open PretorsionImageClosed
universe u v
variable {A : Type u} {X : Type v}
variable [Ring A] [AddCommGroup X] [Module A X]

theorem PretorsionImageClosed.idealRange_top :
    idealRange (⊤ : Ideal (Module.End A X)) = ⊤ := by sorry
