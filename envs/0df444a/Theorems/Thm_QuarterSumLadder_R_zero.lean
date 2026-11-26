-- Prove2me | Theorems.Thm_QuarterSumLadder_R_zero
-- name    : QuarterSumLadder.R_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:04:59.921799+00:00
-- url     : https://prove2.me/theorems/2421715e-0d77-4b94-91e5-30dc0e4ed98d
-- title:
--   Quarter Sum Ladder: R zero
-- statement:
--   The Quarter Sum Ladder construction uses the R zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L56-L57
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L56-L57

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

theorem QuarterSumLadder.R_zero : R χ 0 = ((fiber χ 1).filter fun x => 4 * x.val < p).card := by sorry
