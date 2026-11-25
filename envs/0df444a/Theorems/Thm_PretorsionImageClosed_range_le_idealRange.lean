-- Prove2me | Theorems.Thm_PretorsionImageClosed_range_le_idealRange
-- name    : PretorsionImageClosed.range_le_idealRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:29:49.164284+00:00
-- url     : https://prove2.me/theorems/897d2b96-c1aa-49dd-8bdf-1475c226bf7e
-- title:
--   Pretorsion Image Closed: range le ideal Range
-- statement:
--   Each ideal element's range belongs to the total ideal range.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L200-L205
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L200-L205

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

theorem PretorsionImageClosed.range_le_idealRange
    {I : Ideal (Module.End A X)}
    (f : Module.End A X) (hf : f ∈ I) :
    LinearMap.range f ≤ idealRange I := by sorry
