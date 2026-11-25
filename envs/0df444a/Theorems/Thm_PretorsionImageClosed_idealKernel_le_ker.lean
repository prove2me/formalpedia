-- Prove2me | Theorems.Thm_PretorsionImageClosed_idealKernel_le_ker
-- name    : PretorsionImageClosed.idealKernel_le_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:11:02.090679+00:00
-- url     : https://prove2.me/theorems/e8180bb4-b60a-45cc-8e6c-16b860f69285
-- title:
--   Pretorsion Image Closed: ideal Kernel le ker
-- statement:
--   The common ideal kernel lies in the kernel of each ideal element.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L282-L287
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L282-L287

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

theorem PretorsionImageClosed.idealKernel_le_ker
    {I : Ideal (Module.End A X)}
    (f : Module.End A X) (hf : f ∈ I) :
    idealKernel I ≤ LinearMap.ker f := by sorry
