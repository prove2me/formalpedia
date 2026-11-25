-- Prove2me | Theorems.Thm_SmallRatio_den_le
-- name    : SmallRatio.den_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:20:02.256402+00:00
-- url     : https://prove2.me/theorems/bd463313-5ed3-5145-9927-a84a117d7773
-- title:
--   Small Ratio: den le
-- statement:
--   The Small Ratio construction uses the den le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L190-L194
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L190-L194

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

theorem SmallRatio.den_le {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ steps k h) : den k h j ≤ k := by sorry
