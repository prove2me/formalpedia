-- Prove2me | Theorems.Thm_QuarterSumLadder_neg_one_pow_mul_self
-- name    : QuarterSumLadder.neg_one_pow_mul_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:06:38.865904+00:00
-- url     : https://prove2.me/theorems/c8fe7d1e-e581-43dd-b548-97aa4088a58b
-- title:
--   Quarter Sum Ladder: neg one pow mul self
-- statement:
--   The Quarter Sum Ladder construction uses the neg one pow mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L105-L106
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L105-L106

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

theorem QuarterSumLadder.neg_one_pow_mul_self (n : ℕ) : ((-1 : ZMod p) ^ n) * (-1) ^ n = 1 := by sorry
