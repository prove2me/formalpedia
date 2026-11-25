-- Prove2me | Theorems.Thm_SmallRatio_rem_strictAnti
-- name    : SmallRatio.rem_strictAnti
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:19:35.925825+00:00
-- url     : https://prove2.me/theorems/93b3b9df-ee0f-5999-be34-ec46998150ee
-- title:
--   Small Ratio: rem strict Anti
-- statement:
--   The Small Ratio construction uses the rem strict Anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L108-L115
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L108-L115

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

theorem SmallRatio.rem_strictAnti {i j : ℕ} (hij : i < j) (hj : j ≤ steps k h) : rem k h j < rem k h i := by sorry
