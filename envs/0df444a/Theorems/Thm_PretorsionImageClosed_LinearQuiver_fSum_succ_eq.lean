-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_fSum_succ_eq
-- name    : PretorsionImageClosed.LinearQuiver.fSum_succ_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:22:08.249449+00:00
-- url     : https://prove2.me/theorems/11f02b44-7adb-536b-99dc-27f8a9483a52
-- title:
--   Linear Quiver: f Sum succ eq
-- statement:
--   The Linear Quiver construction uses the f Sum succ eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L412-L423
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L412-L423

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
variable {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.fSum_succ_eq (n : ℕ) :
    fSum (n + 1) = ∑ D : ClosedFamily n, C (q ^ D.1.D.card) * theta (adm D.1) := by sorry
