-- Prove2me | Theorems.Thm_SmallRatio_rem_succ_lt
-- name    : SmallRatio.rem_succ_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:17:44.617075+00:00
-- url     : https://prove2.me/theorems/a08de39d-a6d2-5374-8476-5c802d4678f9
-- title:
--   Small Ratio: rem succ lt
-- statement:
--   The remainders decrease strictly on `[0, n]`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L101-L106
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L101-L106

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

theorem SmallRatio.rem_succ_lt {j : ℕ} (hj : j < steps k h) : rem k h (j + 1) < rem k h j := by sorry
