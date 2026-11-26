-- Prove2me | Theorems.Thm_QuarterSumLadder_b2_trichotomy
-- name    : QuarterSumLadder.b2_trichotomy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:12:29.295062+00:00
-- url     : https://prove2.me/theorems/4a1f6666-95e0-531e-9fae-9ddcc363fb48
-- title:
--   Quarter Sum Ladder: b2 trichotomy
-- statement:
--   **The weight-two trichotomy** (Paper IV, Theorem 8.2), with `N(B₂) = c₀² + c₁²`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Boundary.lean#L132-L199
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Boundary.lean#L132-L199

module
public import Definitions.Def_QuarterSumLadder_Ladder
public import Definitions.Def_QuarterSumLadder_Boundary
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ

theorem QuarterSumLadder.b2_trichotomy :
    (χ 2 = -1 → (32 : ℤ) ∣ (B2 χ).norm ∧ ¬ (64 : ℤ) ∣ (B2 χ).norm) ∧
      (χ 2 = 1 → p % 16 = 9 → (64 : ℤ) ∣ (B2 χ).norm ∧ ¬ (128 : ℤ) ∣ (B2 χ).norm) ∧
      (χ 2 = 1 → p % 16 = 1 → (128 : ℤ) ∣ (B2 χ).norm) := by sorry
