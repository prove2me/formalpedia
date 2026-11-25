-- Prove2me | Theorems.Thm_PretorsionImageClosed_mem_end_jacobson_iff_not_isUnit
-- name    : PretorsionImageClosed.mem_end_jacobson_iff_not_isUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:07:44.331568+00:00
-- url     : https://prove2.me/theorems/d20a32f8-9e60-5679-8ba1-f425d2bec68d
-- title:
--   Pretorsion Image Closed: mem end jacobson iff not is Unit
-- statement:
--   An endomorphism of an indecomposable finite-length module belongs to
--   the Jacobson radical exactly when it is not invertible.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L173-L179
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L173-L179

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

theorem PretorsionImageClosed.mem_end_jacobson_iff_not_isUnit
    (hX : PretorsionImageClosed.IsIndecomposableModule A X)
    (hXlen : IsFiniteLength A X)
    (f : Module.End A X) :
    f ∈ Ring.jacobson (Module.End A X) ↔ ¬ IsUnit f := by sorry
