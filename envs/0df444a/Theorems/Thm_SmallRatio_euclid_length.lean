-- Prove2me | Theorems.Thm_SmallRatio_euclid_length
-- name    : SmallRatio.euclid_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:25:24.115626+00:00
-- url     : https://prove2.me/theorems/8d871a3b-13f3-4055-80e0-524ded0d77f8
-- title:
--   Small Ratio: euclid length
-- statement:
--   **The length of the algorithm:** `n ≤ 2 log₂ k + 1`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/Solution.lean#L48-L50
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/Solution.lean#L48-L50

module
public import Definitions.Def_SmallRatio
public import Definitions.Def_SmallRatios_Solution
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset

theorem SmallRatio.euclid_length {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h) :
    steps k h ≤ 2 * Nat.log 2 k + 1 := by sorry
