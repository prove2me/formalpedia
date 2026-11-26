-- Prove2me | Theorems.Thm_QuarterSumLadder_char_neg
-- name    : QuarterSumLadder.char_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:00:35.184801+00:00
-- url     : https://prove2.me/theorems/46c68a7a-dc4f-5c94-83f8-d9dddccff566
-- title:
--   Quarter Sum Ladder: char neg
-- statement:
--   The Quarter Sum Ladder construction uses the char neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L65-L68
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L65-L68

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

theorem QuarterSumLadder.char_neg (x : ZMod p) : χ (-x) = χ x := by sorry
