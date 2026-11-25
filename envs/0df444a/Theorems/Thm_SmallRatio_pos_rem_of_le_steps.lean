-- Prove2me | Theorems.Thm_SmallRatio_pos_rem_of_le_steps
-- name    : SmallRatio.pos_rem_of_le_steps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:17:54.52381+00:00
-- url     : https://prove2.me/theorems/e1911dbf-8470-449f-adcd-32f9cda1134f
-- title:
--   Small Ratio: pos rem of le steps
-- statement:
--   The Small Ratio construction uses the pos rem of le steps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L95-L98
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L95-L98

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

theorem SmallRatio.pos_rem_of_le_steps {j : ℕ} (hj : j ≤ steps k h) : 0 < rem k h j := by sorry
