-- Prove2me | Theorems.Thm_QuarterSumLadder_gaussMap_mem_half
-- name    : QuarterSumLadder.gaussMap_mem_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:57:54.643809+00:00
-- url     : https://prove2.me/theorems/0a2ee6d2-ecff-533c-a265-6ae0a1cbdc03
-- title:
--   Quarter Sum Ladder: gauss Map mem half
-- statement:
--   The Quarter Sum Ladder construction uses the gauss Map mem half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Prelim.lean#L52-L60
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Prelim.lean#L52-L60

module
public import Definitions.Def_QuarterSumLadder_Defs
public import Definitions.Def_QuarterSumLadder_Prelim
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.gaussMap_mem_half (hp2 : p ≠ 2) {x : ZMod p} (hx0 : x ≠ 0) (hx : 2 * x.val < p) :
    2 * (gaussMap x).val < p := by sorry
