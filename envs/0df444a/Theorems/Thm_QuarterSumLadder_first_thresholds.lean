-- Prove2me | Theorems.Thm_QuarterSumLadder_first_thresholds
-- name    : QuarterSumLadder.first_thresholds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:11:19.23152+00:00
-- url     : https://prove2.me/theorems/bf603e50-24b5-56ef-989d-fb4495786831
-- title:
--   Quarter Sum Ladder: first thresholds
-- statement:
--   **The first three thresholds** (Paper IV, Theorem 5.2), in terms of `N(Ω) = x² + y²`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Ladder.lean#L69-L90
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Ladder.lean#L69-L90

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

theorem QuarterSumLadder.first_thresholds :
    (χ 2 = -1 → (2 : ℤ) ∣ (Omega χ).norm ∧ ¬ (4 : ℤ) ∣ (Omega χ).norm) ∧
      (χ 2 = 1 → p % 16 = 9 → (4 : ℤ) ∣ (Omega χ).norm ∧ ¬ (8 : ℤ) ∣ (Omega χ).norm) ∧
      (χ 2 = 1 → p % 16 = 1 → (8 : ℤ) ∣ (Omega χ).norm) := by sorry
