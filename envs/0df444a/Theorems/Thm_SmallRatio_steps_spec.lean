-- Prove2me | Theorems.Thm_SmallRatio_steps_spec
-- name    : SmallRatio.steps_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:18:29.83326+00:00
-- url     : https://prove2.me/theorems/38cc2775-a2b1-5eb5-8068-066758006928
-- title:
--   Small Ratio: steps spec
-- statement:
--   The Small Ratio construction uses the steps spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L63-L68
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L63-L68

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
omit hh hc

theorem SmallRatio.steps_spec : rem k h (steps k h) ≤ 1 := by sorry
