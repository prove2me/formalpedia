-- Prove2me | Theorems.Thm_SmallRatio_sum_odd
-- name    : SmallRatio.sum_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:15:06.592389+00:00
-- url     : https://prove2.me/theorems/8523a81c-f10d-42b9-ae28-a2d923025b46
-- title:
--   Small Ratio: sum odd
-- statement:
--   `∑_{j=1}^{m} (2j - 1) = m²`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Reciprocity.lean#L130-L136
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Reciprocity.lean#L130-L136

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Reciprocity
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset

theorem SmallRatio.sum_odd (m : ℕ) : ∑ j ∈ Ico 1 (m + 1), (2 * (j : ℤ) - 1) = (m : ℤ) ^ 2 := by sorry
