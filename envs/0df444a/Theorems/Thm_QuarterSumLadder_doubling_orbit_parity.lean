-- Prove2me | Theorems.Thm_QuarterSumLadder_doubling_orbit_parity
-- name    : QuarterSumLadder.doubling_orbit_parity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:17:28.342633+00:00
-- url     : https://prove2.me/theorems/5706553b-4a81-4ed6-8ba5-c05c5b2b9dcf
-- title:
--   Quarter Sum Ladder: doubling orbit parity
-- statement:
--   **Doubling-orbit parity** (Paper IV, Theorem 3.3): if `χ(2) = 1`, then
--   `R₀ ≡ R₁ ≡ R₂ ≡ R₃ (mod 2)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L81-L83
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L81-L83

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.doubling_orbit_parity {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) (hw : χ 2 = 1) :
    R χ 1 % 2 = R χ 0 % 2 ∧ R χ 2 % 2 = R χ 0 % 2 ∧ R χ 3 % 2 = R χ 0 % 2 := by sorry
