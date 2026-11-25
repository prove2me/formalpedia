-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_ofIntervals_prop_interval
-- name    : PretorsionImageClosed.LinearQuiver.ofIntervals_prop_interval
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:14:56.183819+00:00
-- url     : https://prove2.me/theorems/14549d77-fc0e-532b-9f3d-84cf7663f96b
-- title:
--   Linear Quiver: of Intervals prop interval
-- statement:
--   The Linear Quiver construction uses the of Intervals prop interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalSets.lean#L109-L116
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalSets.lean#L109-L116

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Data.Fintype.Powerset
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalSets
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.ofIntervals_prop_interval (S : Fin n → Fin n → Prop) {a d : Fin n} (had : a ≤ d) :
    (ofIntervals (k := k) S).prop (interval k a d) ↔ S a d := by sorry
