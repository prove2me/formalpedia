-- Prove2me | Theorems.Thm_QuarterSumLadder_two_pow_Q
-- name    : QuarterSumLadder.two_pow_Q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:06:47.908384+00:00
-- url     : https://prove2.me/theorems/b3e0023a-e362-4d1b-ad2c-21655bb19230
-- title:
--   Quarter Sum Ladder: two pow Q
-- statement:
--   `2^Q = (-1)^{R₁ + R₃}` in `ZMod p`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L109-L148
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L109-L148

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

theorem QuarterSumLadder.two_pow_Q : (2 : ZMod p) ^ Q p = (-1) ^ (R χ 1 + R χ 3) := by sorry
