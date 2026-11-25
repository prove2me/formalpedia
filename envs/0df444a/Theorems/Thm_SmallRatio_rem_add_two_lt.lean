-- Prove2me | Theorems.Thm_SmallRatio_rem_add_two_lt
-- name    : SmallRatio.rem_add_two_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:19:30.212889+00:00
-- url     : https://prove2.me/theorems/bf7ee04f-49a9-4386-9c40-29ab492057be
-- title:
--   Small Ratio: rem add two lt
-- statement:
--   The Small Ratio construction uses the rem add two lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L39-L40
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L39-L40

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}

theorem SmallRatio.rem_add_two_lt (j : ℕ) (hpos : 0 < rem k h (j + 1)) : rem k h (j + 2) < rem k h (j + 1) := by sorry
