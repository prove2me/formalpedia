-- Prove2me | Theorems.Thm_PretorsionImageClosed_end_jacobson_eq_nonunits
-- name    : PretorsionImageClosed.end_jacobson_eq_nonunits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:13:05.62551+00:00
-- url     : https://prove2.me/theorems/a0a87932-2901-4066-ad27-754c475860c6
-- title:
--   Pretorsion Image Closed: end jacobson eq nonunits
-- statement:
--   The Jacobson radical of the endomorphism ring is exactly its ideal
--   of noninvertible endomorphisms.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L146-L169
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L146-L169

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

theorem PretorsionImageClosed.end_jacobson_eq_nonunits
    (hX : PretorsionImageClosed.IsIndecomposableModule A X)
    (hXlen : IsFiniteLength A X) :
    Ring.jacobson (Module.End A X) =
      endNonunitsIdeal hX hXlen := by sorry
