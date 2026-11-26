-- Prove2me | Theorems.Thm_QuarterSumLadder_gaussMap_char
-- name    : QuarterSumLadder.gaussMap_char
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:05:58.792431+00:00
-- url     : https://prove2.me/theorems/9f0d96f4-e0ed-498f-9671-da1dedfa36ee
-- title:
--   Quarter Sum Ladder: gauss Map char
-- statement:
--   The Quarter Sum Ladder construction uses the gauss Map char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L98-L102
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L98-L102

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

theorem QuarterSumLadder.gaussMap_char (x : ZMod p) : χ (gaussMap x) = χ 2 * χ x := by sorry
