-- Prove2me | Theorems.Thm_QuarterSumLadder_R_one
-- name    : QuarterSumLadder.R_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:05:21.347718+00:00
-- url     : https://prove2.me/theorems/d19e7e40-aa91-491d-bd82-31942582cf1e
-- title:
--   Quarter Sum Ladder: R one
-- statement:
--   The Quarter Sum Ladder construction uses the R one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L60-L61
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L60-L61

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

theorem QuarterSumLadder.R_one : R χ 1 = ((fiber χ gi).filter fun x => 4 * x.val < p).card := by sorry
