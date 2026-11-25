-- Prove2me | Theorems.Thm_SmallRatio_steps_le_log
-- name    : SmallRatio.steps_le_log
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:20:34.856534+00:00
-- url     : https://prove2.me/theorems/757b8302-e947-4b31-91fd-4a7f8671ec88
-- title:
--   Small Ratio: steps le log
-- statement:
--   `n ≤ 2 log₂ k + 1`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L229-L240
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L229-L240

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}
variable (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc

theorem SmallRatio.steps_le_log : steps k h ≤ 2 * Nat.log 2 k + 1 := by sorry
