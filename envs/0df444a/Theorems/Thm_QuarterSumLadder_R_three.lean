-- Prove2me | Theorems.Thm_QuarterSumLadder_R_three
-- name    : QuarterSumLadder.R_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:05:21.110542+00:00
-- url     : https://prove2.me/theorems/90b58763-5139-4f16-95bb-b664b81adba5
-- title:
--   Quarter Sum Ladder: R three
-- statement:
--   The Quarter Sum Ladder construction uses the R three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L68-L69
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L68-L69

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

theorem QuarterSumLadder.R_three : R χ 3 = ((fiber χ (-gi)).filter fun x => 4 * x.val < p).card := by sorry
