-- Prove2me | Theorems.Thm_QuarterSumLadder_fourth_threshold
-- name    : QuarterSumLadder.fourth_threshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:10:15.988213+00:00
-- url     : https://prove2.me/theorems/7894b047-7f7d-4f10-aba9-a14aeac9a0f8
-- title:
--   Quarter Sum Ladder: fourth threshold
-- statement:
--   **The fourth threshold** (Paper IV, Theorem 5.3): if `χ(2) = 1` and `p ≡ 1 (mod 16)`, then
--   `16 ∣ N(Ω) ⟺ R₁ + 2R₂ + R₃ ≡ 0 (mod 4)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Ladder.lean#L94-L103
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Ladder.lean#L94-L103

module
public import Definitions.Def_QuarterSumLadder_WeightTwo
public import Definitions.Def_QuarterSumLadder_Arith
public import Definitions.Def_QuarterSumLadder_Ladder
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ

theorem QuarterSumLadder.fourth_threshold (hw : χ 2 = 1) (h16 : p % 16 = 1) :
    (16 : ℤ) ∣ (Omega χ).norm ↔ (R χ 1 + 2 * R χ 2 + R χ 3) % 4 = 0 := by sorry
