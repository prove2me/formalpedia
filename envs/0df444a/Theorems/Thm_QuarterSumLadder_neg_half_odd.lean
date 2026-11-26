-- Prove2me | Theorems.Thm_QuarterSumLadder_neg_half_odd
-- name    : QuarterSumLadder.neg_half_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:01:09.553113+00:00
-- url     : https://prove2.me/theorems/8e2fc325-6ec6-41fb-9cdc-8451e6d49a30
-- title:
--   Quarter Sum Ladder: neg half odd
-- statement:
--   The Quarter Sum Ladder construction uses the neg half odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L160-L164
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L160-L164

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
omit hp8 hχ

theorem QuarterSumLadder.neg_half_odd (hp2 : p ≠ 2) {x : ZMod p} (hx : x ≠ 0) :
    (Odd (-x).val ↔ ¬ Odd x.val) := by sorry
