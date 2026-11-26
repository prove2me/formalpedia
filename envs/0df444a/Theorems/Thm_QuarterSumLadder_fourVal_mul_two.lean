-- Prove2me | Theorems.Thm_QuarterSumLadder_fourVal_mul_two
-- name    : QuarterSumLadder.fourVal_mul_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:09:10.372818+00:00
-- url     : https://prove2.me/theorems/b2f2547b-6271-4ed4-9137-b53093932f7e
-- title:
--   Quarter Sum Ladder: four Val mul two
-- statement:
--   The Quarter Sum Ladder construction uses the four Val mul two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L195-L197
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L195-L197

module
public import Definitions.Def_QuarterSumLadder_Counts
public import Definitions.Def_QuarterSumLadder_WeightTwo
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ

theorem QuarterSumLadder.fourVal_mul_two {z : GaussianInt} (hz : FourVal z) : FourVal (χ 2 * z) := by sorry
