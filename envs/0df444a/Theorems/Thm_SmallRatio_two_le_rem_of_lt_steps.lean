-- Prove2me | Theorems.Thm_SmallRatio_two_le_rem_of_lt_steps
-- name    : SmallRatio.two_le_rem_of_lt_steps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:19:10.024053+00:00
-- url     : https://prove2.me/theorems/09c6e13b-aa2c-421b-84dc-08b51e0d684d
-- title:
--   Small Ratio: two le rem of lt steps
-- statement:
--   The Small Ratio construction uses the two le rem of lt steps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L71-L74
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L71-L74

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
omit hh hhk hc

theorem SmallRatio.two_le_rem_of_lt_steps {j : ℕ} (hj : j < steps k h) : 2 ≤ rem k h j := by sorry
