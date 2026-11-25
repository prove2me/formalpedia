-- Prove2me | Theorems.Thm_SmallRatio_den_pos
-- name    : SmallRatio.den_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:19:24.398507+00:00
-- url     : https://prove2.me/theorems/8a670d57-951a-4637-adcd-88c73c904b9d
-- title:
--   Small Ratio: den pos
-- statement:
--   The Small Ratio construction uses the den pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L170-L180
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L170-L180

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

theorem SmallRatio.den_pos {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ steps k h + 1) : 1 ≤ den k h j := by sorry
