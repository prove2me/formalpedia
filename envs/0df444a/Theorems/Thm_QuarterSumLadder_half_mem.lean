-- Prove2me | Theorems.Thm_QuarterSumLadder_half_mem
-- name    : QuarterSumLadder.half_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:05:34.348001+00:00
-- url     : https://prove2.me/theorems/3a01a7d4-f97d-4b32-913f-b138e4ccd2b3
-- title:
--   Quarter Sum Ladder: half mem
-- statement:
--   The Quarter Sum Ladder construction uses the half mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L87-L87
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L87-L87

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
omit hp hp8 hχ

theorem QuarterSumLadder.half_mem {x : ZMod p} (h : 4 * x.val < p) : 2 * x.val < p := by sorry
