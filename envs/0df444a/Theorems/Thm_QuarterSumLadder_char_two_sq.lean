-- Prove2me | Theorems.Thm_QuarterSumLadder_char_two_sq
-- name    : QuarterSumLadder.char_two_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:59:58.227441+00:00
-- url     : https://prove2.me/theorems/9cc4f436-3c0a-54a5-b664-755beffc5f77
-- title:
--   Quarter Sum Ladder: char two sq
-- statement:
--   The Quarter Sum Ladder construction uses the char two sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L77-L78
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L77-L78

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

theorem QuarterSumLadder.char_two_sq : χ 2 * χ 2 = 1 := by sorry
