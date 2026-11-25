-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_interval_iso_iff
-- name    : PretorsionImageClosed.LinearQuiver.interval_iso_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:07:28.528166+00:00
-- url     : https://prove2.me/theorems/1a5df23f-2493-4b4c-966b-052657071047
-- title:
--   Linear Quiver: interval iso iff
-- statement:
--   The Linear Quiver construction uses the interval iso iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L122-L150
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L122-L150

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.interval_iso_iff {a d a' d' : Fin n} (had : a ≤ d) (had' : a' ≤ d') :
    Nonempty (interval k a d ≅ interval k a' d') ↔ a = a' ∧ d = d' := by sorry
