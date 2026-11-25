-- Prove2me | Theorems.Thm_SmallRatio_rem_add_two
-- name    : SmallRatio.rem_add_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:17:35.194838+00:00
-- url     : https://prove2.me/theorems/1f0240b9-5b87-59f5-bcda-f401edfbfe1c
-- title:
--   Small Ratio: rem add two
-- statement:
--   The Small Ratio construction uses the rem add two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L27-L27
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L27-L27

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}

theorem SmallRatio.rem_add_two (j : ℕ) : rem k h (j + 2) = rem k h j % rem k h (j + 1) := by sorry
