-- Prove2me | Theorems.Thm_QuarterSumLadder_weight_two_trichotomy
-- name    : QuarterSumLadder.weight_two_trichotomy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:17:51.802561+00:00
-- url     : https://prove2.me/theorems/78a1253c-c946-57bf-b113-2abb3ef493ad
-- title:
--   Quarter Sum Ladder: weight two trichotomy
-- statement:
--   **The weight-two trichotomy** (Paper IV, Theorem 8.2), with `N(B₂) = c₀² + c₁²`: `32 ∥ N(B₂)` if
--   `χ(2) = -1`; `64 ∥ N(B₂)` if `χ(2) = 1`, `p ≡ 9 (mod 16)`; `128 ∣ N(B₂)` if `χ(2) = 1`, `p ≡ 1 (mod 16)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L168-L172
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L168-L172

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.weight_two_trichotomy {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    (χ 2 = -1 → (32 : ℤ) ∣ (B2 χ).norm ∧ ¬ (64 : ℤ) ∣ (B2 χ).norm) ∧
      (χ 2 = 1 → p % 16 = 9 → (64 : ℤ) ∣ (B2 χ).norm ∧ ¬ (128 : ℤ) ∣ (B2 χ).norm) ∧
      (χ 2 = 1 → p % 16 = 1 → (128 : ℤ) ∣ (B2 χ).norm) := by sorry
