-- Prove2me | Theorems.Thm_PretorsionImageClosed_map_idealRange_le
-- name    : PretorsionImageClosed.map_idealRange_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:13:08.489492+00:00
-- url     : https://prove2.me/theorems/646eb8d3-c5b3-4a32-bc65-73951bbc870d
-- title:
--   Pretorsion Image Closed: map ideal Range le
-- statement:
--   Acting by an element of `I` sends the range of `J` into the range
--   of the product ideal `I * J`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L230-L239
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L230-L239

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

theorem PretorsionImageClosed.map_idealRange_le
    {I J : Ideal (Module.End A X)}
    (f : Module.End A X) (hf : f ∈ I) :
    Submodule.map f (idealRange J) ≤ idealRange (I * J) := by sorry
