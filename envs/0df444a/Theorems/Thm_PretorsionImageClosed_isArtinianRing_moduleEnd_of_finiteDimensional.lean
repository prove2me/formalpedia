-- Prove2me | Theorems.Thm_PretorsionImageClosed_isArtinianRing_moduleEnd_of_finiteDimensional
-- name    : PretorsionImageClosed.isArtinianRing_moduleEnd_of_finiteDimensional
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:09:14.947341+00:00
-- url     : https://prove2.me/theorems/5bc2de8f-afaa-593f-aa92-2e74316eae2d
-- title:
--   Pretorsion Image Closed: is Artinian Ring module End of finite Dimensional
-- statement:
--   The endomorphism ring of a module finite-dimensional over a central
--   ground field is Artinian.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L183-L193
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L183-L193

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

theorem PretorsionImageClosed.isArtinianRing_moduleEnd_of_finiteDimensional
    {K B M : Type*}
    [Field K] [Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module B M]
    [IsScalarTower K B M] [FiniteDimensional K M] :
    IsArtinianRing (Module.End B M) := by sorry
