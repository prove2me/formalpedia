-- Prove2me | Theorems.Thm_QuarterSumLadder_char_even
-- name    : QuarterSumLadder.char_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:00:17.822197+00:00
-- url     : https://prove2.me/theorems/d72602c1-9f63-5de2-99cc-c1dd1c712088
-- title:
--   Quarter Sum Ladder: char even
-- statement:
--   The Quarter Sum Ladder construction uses the char even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L59-L59
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L59-L59

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

theorem QuarterSumLadder.char_even : χ (-1) = 1 := by sorry
