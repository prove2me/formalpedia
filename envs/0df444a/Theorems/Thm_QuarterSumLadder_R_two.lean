-- Prove2me | Theorems.Thm_QuarterSumLadder_R_two
-- name    : QuarterSumLadder.R_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:05:15.5816+00:00
-- url     : https://prove2.me/theorems/a3863106-d3df-4504-ba51-94dc490488e4
-- title:
--   Quarter Sum Ladder: R two
-- statement:
--   The Quarter Sum Ladder construction uses the R two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L64-L65
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L64-L65

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
omit hp8 hχ

theorem QuarterSumLadder.R_two : R χ 2 = ((fiber χ (-1)).filter fun x => 4 * x.val < p).card := by sorry
