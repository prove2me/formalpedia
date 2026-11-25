-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_xSum_eq
-- name    : PretorsionImageClosed.LinearQuiver.xSum_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:26:59.030481+00:00
-- url     : https://prove2.me/theorems/aa8b741b-aba6-4edf-8b55-248b1b4d0aff
-- title:
--   Linear Quiver: x Sum eq
-- statement:
--   Theorem 8.5 in terms of families: `xSum n = C_{n+1}`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L511-L514
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L511-L514

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

theorem PretorsionImageClosed.LinearQuiver.xSum_eq (n : ℕ) : xSum n = gandhiSecondOf (n + 1) := by sorry
