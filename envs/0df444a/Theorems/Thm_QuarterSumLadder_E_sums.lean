-- Prove2me | Theorems.Thm_QuarterSumLadder_E_sums
-- name    : QuarterSumLadder.E_sums
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:09:43.425777+00:00
-- url     : https://prove2.me/theorems/27daf7c7-14a1-4f3d-98a6-d91ff40a5454
-- title:
--   Quarter Sum Ladder: E sums
-- statement:
--   `E₁ + E₋₁ = R₁ + R₃` and `E_i + E_{-i} = R₀ + R₂`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L217-L225
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L217-L225

module
public import Definitions.Def_QuarterSumLadder_Counts
public import Definitions.Def_QuarterSumLadder_WeightTwo
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ

theorem QuarterSumLadder.E_sums : E χ 1 + E χ (-1) = R χ 1 + R χ 3 ∧ E χ gi + E χ (-gi) = R χ 0 + R χ 2 := by sorry
