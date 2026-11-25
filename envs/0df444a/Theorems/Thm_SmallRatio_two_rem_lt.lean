-- Prove2me | Theorems.Thm_SmallRatio_two_rem_lt
-- name    : SmallRatio.two_rem_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:20:02.05252+00:00
-- url     : https://prove2.me/theorems/dae43127-57fa-5a35-80d0-faf87c35fc73
-- title:
--   Small Ratio: two rem lt
-- statement:
--   `2 r_{j+2} < r_j` for `j + 2 ≤ n`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L197-L210
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L197-L210

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

theorem SmallRatio.two_rem_lt {j : ℕ} (hj : j + 1 < steps k h) : 2 * rem k h (j + 2) < rem k h j := by sorry
