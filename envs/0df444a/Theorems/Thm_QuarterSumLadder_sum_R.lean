-- Prove2me | Theorems.Thm_QuarterSumLadder_sum_R
-- name    : QuarterSumLadder.sum_R
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:06:01.852548+00:00
-- url     : https://prove2.me/theorems/92fa43ea-3858-4fbe-99f6-1b4611d696d0
-- title:
--   Quarter Sum Ladder: sum R
-- statement:
--   `R₀ + R₁ + R₂ + R₃ = Q`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L72-L84
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L72-L84

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

theorem QuarterSumLadder.sum_R : R χ 0 + R χ 1 + R χ 2 + R χ 3 = Q p := by sorry
