-- Prove2me | Theorems.Thm_SmallRatio_rem_div_rem_pos
-- name    : SmallRatio.rem_div_rem_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:17:48.253397+00:00
-- url     : https://prove2.me/theorems/cd964b9f-6232-567c-9650-e83c7d4d49da
-- title:
--   Small Ratio: rem div rem pos
-- statement:
--   The Small Ratio construction uses the rem div rem pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L122-L125
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L122-L125

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

theorem SmallRatio.rem_div_rem_pos {j : ℕ} (hj : j < steps k h) : 1 ≤ rem k h j / rem k h (j + 1) := by sorry
