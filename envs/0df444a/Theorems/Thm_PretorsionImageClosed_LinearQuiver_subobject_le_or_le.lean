-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_subobject_le_or_le
-- name    : PretorsionImageClosed.LinearQuiver.subobject_le_or_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:08:17.8379+00:00
-- url     : https://prove2.me/theorems/d3448882-e7a0-58b4-9210-12c8f8bdac9e
-- title:
--   Linear Quiver: subobject le or le
-- statement:
--   Subobjects of an interval are totally ordered.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/SummandReduction.lean#L100-L105
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/SummandReduction.lean#L100-L105

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction
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

theorem PretorsionImageClosed.LinearQuiver.subobject_le_or_le {a d : Fin n} (K K' : Subobject (interval k a d)) : K ≤ K' ∨ K' ≤ K := by sorry
