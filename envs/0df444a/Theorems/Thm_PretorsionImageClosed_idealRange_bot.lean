-- Prove2me | Theorems.Thm_PretorsionImageClosed_idealRange_bot
-- name    : PretorsionImageClosed.idealRange_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:08:34.27145+00:00
-- url     : https://prove2.me/theorems/dd4be5b3-ebc5-501c-8ca0-5235e341ca05
-- title:
--   Pretorsion Image Closed: ideal Range bot
-- statement:
--   The Pretorsion Image Closed construction uses the ideal Range bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L208-L215
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L208-L215

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

theorem PretorsionImageClosed.idealRange_bot :
    idealRange (⊥ : Ideal (Module.End A X)) = ⊥ := by sorry
