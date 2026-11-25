-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_exists_iso_interval_of_indecomposable
-- name    : PretorsionImageClosed.LinearQuiver.exists_iso_interval_of_indecomposable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:07:21.202716+00:00
-- url     : https://prove2.me/theorems/199bc6ca-aa60-4838-90a3-8f0adac3b9cb
-- title:
--   Linear Quiver: exists iso interval of indecomposable
-- statement:
--   The Linear Quiver construction uses the exists iso interval of indecomposable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L154-L159
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L154-L159

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

theorem PretorsionImageClosed.LinearQuiver.exists_iso_interval_of_indecomposable {X : Statement.LinRep k n} (hX : Indecomposable X) :
    ∃ a d : Fin n, a ≤ d ∧ Nonempty (X ≅ interval k a d) := by sorry
