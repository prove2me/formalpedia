-- Prove2me | Theorems.Thm_PretorsionImageClosed_mem_endNonunitsIdeal_iff
-- name    : PretorsionImageClosed.mem_endNonunitsIdeal_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:05:15.688271+00:00
-- url     : https://prove2.me/theorems/7ad0f10e-4727-5641-9838-2d04b53eef64
-- title:
--   Pretorsion Image Closed: mem end Nonunits Ideal iff
-- statement:
--   The Pretorsion Image Closed construction uses the mem end Nonunits Ideal iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L119-L124
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L119-L124

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

theorem PretorsionImageClosed.mem_endNonunitsIdeal_iff
    (hX : PretorsionImageClosed.IsIndecomposableModule A X)
    (hXlen : IsFiniteLength A X)
    (f : Module.End A X) :
    f ∈ endNonunitsIdeal hX hXlen ↔ ¬ IsUnit f := by sorry
