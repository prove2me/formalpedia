-- Prove2me | Theorems.Thm_QuarterSumLadder_neg_one_pow_eq_iff
-- name    : QuarterSumLadder.neg_one_pow_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:06:44.090087+00:00
-- url     : https://prove2.me/theorems/d553e8da-780c-504f-9040-e55f9b2df5a2
-- title:
--   Quarter Sum Ladder: neg one pow eq iff
-- statement:
--   The Quarter Sum Ladder construction uses the neg one pow eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L215-L221
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L215-L221

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

theorem QuarterSumLadder.neg_one_pow_eq_iff (hp2 : p ≠ 2) (a b : ℕ) :
    (-1 : ZMod p) ^ a = (-1) ^ b ↔ a % 2 = b % 2 := by sorry
