-- Prove2me | Theorems.Thm_PretorsionImageClosed_idealKernel_bot
-- name    : PretorsionImageClosed.idealKernel_bot
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:05:46.80498+00:00
-- url     : https://prove2.me/theorems/a54dd740-b7b4-52ef-98a8-529d9f6cab28
-- title:
--   Pretorsion Image Closed: ideal Kernel bot
-- statement:
--   The Pretorsion Image Closed construction uses the ideal Kernel bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L290-L297
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L290-L297

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

theorem PretorsionImageClosed.idealKernel_bot :
    idealKernel (⊥ : Ideal (Module.End A X)) = ⊤ := by sorry
