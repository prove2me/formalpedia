-- Prove2me | Theorems.Thm_QuarterSumLadder_ne_zero_of_mem_fiber
-- name    : QuarterSumLadder.ne_zero_of_mem_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:00:11.208137+00:00
-- url     : https://prove2.me/theorems/edeec5a8-2c90-4e60-bf35-da4367885650
-- title:
--   Quarter Sum Ladder: ne zero of mem fiber
-- statement:
--   The Quarter Sum Ladder construction uses the ne zero of mem fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L81-L83
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L81-L83

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

theorem QuarterSumLadder.ne_zero_of_mem_fiber {x : ZMod p} {z : GaussianInt} (hz : z ≠ 0) (hx : x ∈ fiber χ z) :
    x ≠ 0 := by sorry
