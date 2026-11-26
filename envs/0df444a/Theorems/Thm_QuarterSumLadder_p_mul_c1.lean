-- Prove2me | Theorems.Thm_QuarterSumLadder_p_mul_c1
-- name    : QuarterSumLadder.p_mul_c1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:08:29.590819+00:00
-- url     : https://prove2.me/theorems/1c1bb2a1-c19b-410a-b8de-3121591e64ea
-- title:
--   Quarter Sum Ladder: p mul c1
-- statement:
--   The Quarter Sum Ladder construction uses the p mul c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L108-L109
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L108-L109

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

theorem QuarterSumLadder.p_mul_c1 : (p : ℤ) * c1 χ = U χ gi - U χ (-gi) := by sorry
