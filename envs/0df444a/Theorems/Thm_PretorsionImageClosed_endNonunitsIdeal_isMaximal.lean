-- Prove2me | Theorems.Thm_PretorsionImageClosed_endNonunitsIdeal_isMaximal
-- name    : PretorsionImageClosed.endNonunitsIdeal_isMaximal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:12:26.478074+00:00
-- url     : https://prove2.me/theorems/465ee849-a6b4-501e-a81a-d17eafdddbb2
-- title:
--   Pretorsion Image Closed: end Nonunits Ideal is Maximal
-- statement:
--   The ideal of noninvertible endomorphisms is maximal.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L127-L142
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L127-L142

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

theorem PretorsionImageClosed.endNonunitsIdeal_isMaximal
    (hX : PretorsionImageClosed.IsIndecomposableModule A X)
    (hXlen : IsFiniteLength A X) :
    (endNonunitsIdeal hX hXlen).IsMaximal := by sorry
