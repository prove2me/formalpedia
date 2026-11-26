-- Prove2me | Theorems.Thm_QuarterSumLadder_R_eq
-- name    : QuarterSumLadder.R_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:02:31.129448+00:00
-- url     : https://prove2.me/theorems/64a2614c-749c-442f-a744-291ff02db363
-- title:
--   Quarter Sum Ladder: R eq
-- statement:
--   `R_r` counts the elements of the class of `i^r` in `(0, p/4)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L182-L197
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L182-L197

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

theorem QuarterSumLadder.R_eq (r : ℕ) : R χ r = ((fiber χ (gi ^ r)).filter fun x => 4 * x.val < p).card := by sorry
