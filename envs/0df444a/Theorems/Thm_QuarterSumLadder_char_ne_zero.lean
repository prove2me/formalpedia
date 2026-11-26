-- Prove2me | Theorems.Thm_QuarterSumLadder_char_ne_zero
-- name    : QuarterSumLadder.char_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:00:30.839696+00:00
-- url     : https://prove2.me/theorems/5b37befa-718f-5e10-a1b8-e03e348053cc
-- title:
--   Quarter Sum Ladder: char ne zero
-- statement:
--   The Quarter Sum Ladder construction uses the char ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L62-L63
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L62-L63

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
omit hp8

theorem QuarterSumLadder.char_ne_zero {x : ZMod p} (hx : x ≠ 0) : χ x ≠ 0 := by sorry
