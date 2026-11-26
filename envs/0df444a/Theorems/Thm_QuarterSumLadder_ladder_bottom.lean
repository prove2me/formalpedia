-- Prove2me | Theorems.Thm_QuarterSumLadder_ladder_bottom
-- name    : QuarterSumLadder.ladder_bottom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:17:16.855852+00:00
-- url     : https://prove2.me/theorems/a4ad3299-70ad-5ded-829b-11add447c0a8
-- title:
--   Quarter Sum Ladder: ladder bottom
-- statement:
--   **The first three thresholds** (Paper IV, Theorem 5.2), with `N(Ω) = x² + y²`: `2 ∥ N(Ω)` if
--   `χ(2) = -1`; `4 ∥ N(Ω)` if `χ(2) = 1`, `p ≡ 9 (mod 16)`; `8 ∣ N(Ω)` if `χ(2) = 1`, `p ≡ 1 (mod 16)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L102-L106
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L102-L106

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.ladder_bottom {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    (χ 2 = -1 → (2 : ℤ) ∣ (Omega χ).norm ∧ ¬ (4 : ℤ) ∣ (Omega χ).norm) ∧
      (χ 2 = 1 → p % 16 = 9 → (4 : ℤ) ∣ (Omega χ).norm ∧ ¬ (8 : ℤ) ∣ (Omega χ).norm) ∧
      (χ 2 = 1 → p % 16 = 1 → (8 : ℤ) ∣ (Omega χ).norm) := by sorry
