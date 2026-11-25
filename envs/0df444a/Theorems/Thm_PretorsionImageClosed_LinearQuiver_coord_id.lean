-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_id
-- name    : PretorsionImageClosed.LinearQuiver.coord_id
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:27:29.14247+00:00
-- url     : https://prove2.me/theorems/331e7b58-fe3e-4473-b45f-f9bfb2b7d0b6
-- title:
--   Linear Quiver: coord id
-- statement:
--   The Linear Quiver construction uses the coord id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L47-L51
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L47-L51

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

theorem PretorsionImageClosed.LinearQuiver.coord_id (a d i : Fin n) : coord (𝟙 (interval k a d)) i = if a ≤ i ∧ i ≤ d then 1 else 0 := by sorry
