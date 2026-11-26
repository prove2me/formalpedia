-- Prove2me | Theorems.Thm_QuarterSumLadder_exists_char_eq
-- name    : QuarterSumLadder.exists_char_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:01:10.945086+00:00
-- url     : https://prove2.me/theorems/6bd2c12f-55bb-4cdb-94da-3a45eb5a51a8
-- title:
--   Quarter Sum Ladder: exists char eq
-- statement:
--   The Quarter Sum Ladder construction uses the exists char eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L110-L125
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L110-L125

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

theorem QuarterSumLadder.exists_char_eq {z : GaussianInt} (hz : FourVal z) : ∃ c : ZMod p, c ≠ 0 ∧ χ c = z := by sorry
