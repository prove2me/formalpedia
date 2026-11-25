-- Prove2me | Theorems.Thm_SmallRatio_dedekindSum_zero_left
-- name    : SmallRatio.dedekindSum_zero_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:22:21.32768+00:00
-- url     : https://prove2.me/theorems/c86623ad-3bee-4292-bd89-e8f5b1d8bb29
-- title:
--   Small Ratio: dedekind Sum zero left
-- statement:
--   The Small Ratio construction uses the dedekind Sum zero left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Subgroup.lean#L22-L23
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Subgroup.lean#L22-L23

module
public import Definitions.Def_SmallRatio_Main
public import Definitions.Def_SmallRatio_Subgroup
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {p : ℕ}

theorem SmallRatio.dedekindSum_zero_left (k : ℕ) : dedekindSum 0 k = 0 := by sorry
