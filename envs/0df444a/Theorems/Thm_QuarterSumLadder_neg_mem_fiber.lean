-- Prove2me | Theorems.Thm_QuarterSumLadder_neg_mem_fiber
-- name    : QuarterSumLadder.neg_mem_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:00:13.924644+00:00
-- url     : https://prove2.me/theorems/14ab467b-ecd9-4d11-b869-07f1f71f45c6
-- title:
--   Quarter Sum Ladder: neg mem fiber
-- statement:
--   The Quarter Sum Ladder construction uses the neg mem fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L70-L71
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L70-L71

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

theorem QuarterSumLadder.neg_mem_fiber {x : ZMod p} {z : GaussianInt} (h : x ∈ fiber χ z) : -x ∈ fiber χ z := by sorry
