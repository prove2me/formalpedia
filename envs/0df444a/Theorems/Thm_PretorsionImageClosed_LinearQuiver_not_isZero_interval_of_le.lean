-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_not_isZero_interval_of_le
-- name    : PretorsionImageClosed.LinearQuiver.not_isZero_interval_of_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:02:02.336879+00:00
-- url     : https://prove2.me/theorems/5b3ab399-7bd4-583b-af63-50cfb5d2772b
-- title:
--   Linear Quiver: not is Zero interval of le
-- statement:
--   The Linear Quiver construction uses the not is Zero interval of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L60-L61
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L60-L61

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

theorem PretorsionImageClosed.LinearQuiver.not_isZero_interval_of_le {a d : Fin n} (h : a ≤ d) : ¬ IsZero (interval k a d) := by sorry
