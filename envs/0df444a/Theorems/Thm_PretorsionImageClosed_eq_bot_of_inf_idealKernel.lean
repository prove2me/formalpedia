-- Prove2me | Theorems.Thm_PretorsionImageClosed_eq_bot_of_inf_idealKernel
-- name    : PretorsionImageClosed.eq_bot_of_inf_idealKernel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:11:22.935031+00:00
-- url     : https://prove2.me/theorems/36dde3bf-12e0-571e-a766-a5c28d3a4f51
-- title:
--   Pretorsion Image Closed: eq bot of inf ideal Kernel
-- statement:
--   If a fully invariant submodule meets the common kernel of a
--   nilpotent ideal trivially, then the submodule itself is trivial.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L312-L364
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L312-L364

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

theorem PretorsionImageClosed.eq_bot_of_inf_idealKernel
    (I : Ideal (Module.End A X)) [I.IsTwoSided]
    (K : Submodule A X)
    (hK : ∀ f : Module.End A X, Submodule.map f K ≤ K)
    (hI : IsNilpotent I)
    (hinf : K ⊓ idealKernel I = ⊥) :
    K = ⊥ := by sorry
