-- Prove2me | Theorems.Thm_QuarterSumLadder_neg_one_ne_one_zmod
-- name    : QuarterSumLadder.neg_one_ne_one_zmod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:05:17.317541+00:00
-- url     : https://prove2.me/theorems/ac7368a1-86bb-4f69-8f07-b296f33f2345
-- title:
--   Quarter Sum Ladder: neg one ne one zmod
-- statement:
--   The Quarter Sum Ladder construction uses the neg one ne one zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L166-L169
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L166-L169

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

theorem QuarterSumLadder.neg_one_ne_one_zmod (hp2 : p ≠ 2) : (-1 : ZMod p) ≠ 1 := by sorry
