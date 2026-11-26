-- Prove2me | Theorems.Thm_QuarterSumLadder_weight_two_coefficient_congruence
-- name    : QuarterSumLadder.weight_two_coefficient_congruence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:16:34.259373+00:00
-- url     : https://prove2.me/theorems/c0ef0abf-d778-5211-8af6-8d09ed179371
-- title:
--   Quarter Sum Ladder: weight two coefficient congruence
-- statement:
--   **The coefficientwise weight-two congruence** (Paper IV, Theorem 3.1, at order `M = 4`):
--   `c₀ ≡ 4(E₁ + E₋₁)`, `c₁ ≡ 4(E_i + E_{-i})` and `c₀ + c₁ ≡ p - 1 (mod 8)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L45-L48
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L45-L48

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.weight_two_coefficient_congruence {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    c0 χ ≡ 4 * (E χ 1 + E χ (-1)) [ZMOD 8] ∧ c1 χ ≡ 4 * (E χ gi + E χ (-gi)) [ZMOD 8] ∧
      c0 χ + c1 χ ≡ p - 1 [ZMOD 8] := by sorry
