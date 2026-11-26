-- Prove2me | Theorems.Thm_QuarterSumLadder_val_half_of_even
-- name    : QuarterSumLadder.val_half_of_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:00:13.248428+00:00
-- url     : https://prove2.me/theorems/3aa77f38-4271-5c37-bc6f-2ab45f27d330
-- title:
--   Quarter Sum Ladder: val half of even
-- statement:
--   The Quarter Sum Ladder construction uses the val half of even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L200-L202
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L200-L202

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

theorem QuarterSumLadder.val_half_of_even {y : ZMod p} (hy : Even y.val) : (2 * (y.val / 2 : ℕ) : ZMod p) = y := by sorry
