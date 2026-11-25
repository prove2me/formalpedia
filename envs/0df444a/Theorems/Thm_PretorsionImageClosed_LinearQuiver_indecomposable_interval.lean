-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_indecomposable_interval
-- name    : PretorsionImageClosed.LinearQuiver.indecomposable_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:07:11.298664+00:00
-- url     : https://prove2.me/theorems/5ec6718b-00a5-4df7-b44f-ffe6841cb255
-- title:
--   Linear Quiver: indecomposable interval
-- statement:
--   The Linear Quiver construction uses the indecomposable interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L74-L114
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L74-L114

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

theorem PretorsionImageClosed.LinearQuiver.indecomposable_interval {a d : Fin n} (had : a ≤ d) : Indecomposable (interval k a d) := by sorry
