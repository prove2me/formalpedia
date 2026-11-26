-- Prove2me | Theorems.Thm_QuarterSumLadder_p_dvd_U
-- name    : QuarterSumLadder.p_dvd_U
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:08:28.987808+00:00
-- url     : https://prove2.me/theorems/84ed626b-ab40-41cb-bc8e-c755675a13c9
-- title:
--   Quarter Sum Ladder: p dvd U
-- statement:
--   **Divisibility**: `p ∣ U_z` for each class.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L66-L103
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L66-L103

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

theorem QuarterSumLadder.p_dvd_U {z : GaussianInt} : (p : ℤ) ∣ U χ z := by sorry
