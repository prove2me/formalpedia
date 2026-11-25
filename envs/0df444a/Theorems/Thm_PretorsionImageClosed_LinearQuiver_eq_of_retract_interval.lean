-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_of_retract_interval
-- name    : PretorsionImageClosed.LinearQuiver.eq_of_retract_interval
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:15:43.08169+00:00
-- url     : https://prove2.me/theorems/e1b44b07-5782-45e0-ba07-08e3b8e01796
-- title:
--   Linear Quiver: eq of retract interval
-- statement:
--   An interval which is a retract of another interval equals it.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalSets.lean#L86-L92
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalSets.lean#L86-L92

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

theorem PretorsionImageClosed.LinearQuiver.eq_of_retract_interval {a d a' d' : Fin n} (had : a ≤ d) (had' : a' ≤ d')
    (h : Retract (interval k a' d') (interval k a d)) : a' = a ∧ d' = d := by sorry
