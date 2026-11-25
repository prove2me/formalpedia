-- Prove2me | Theorems.Thm_SmallRatio_rem_le_h
-- name    : SmallRatio.rem_le_h
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:19:39.811825+00:00
-- url     : https://prove2.me/theorems/bbfeee92-10c2-56af-8403-5e653c620d4f
-- title:
--   Small Ratio: rem le h
-- statement:
--   The Small Ratio construction uses the rem le h property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L117-L120
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L117-L120

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

theorem SmallRatio.rem_le_h {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ steps k h) : rem k h j ≤ h := by sorry
