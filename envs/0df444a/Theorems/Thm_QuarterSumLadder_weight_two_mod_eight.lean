-- Prove2me | Theorems.Thm_QuarterSumLadder_weight_two_mod_eight
-- name    : QuarterSumLadder.weight_two_mod_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:16:57.650585+00:00
-- url     : https://prove2.me/theorems/f094cfa5-0da9-4beb-b855-ac57e294d0ba
-- title:
--   Quarter Sum Ladder: weight two mod eight
-- statement:
--   **The mod-8 criterion** (Paper IV, Theorem 3.2, without Gauss's criterion `p = a² + 64b²`):
--   `8 ∣ c₀ ∧ 8 ∣ c₁ ⟺ χ(2) = 1 ⟺ 2` is a fourth power modulo `p`; moreover `c₀ ≡ c₁ ≡ 4(R₁ + R₃) (mod 8)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L52-L55
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L52-L55

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.weight_two_mod_eight {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    ((8 : ℤ) ∣ c0 χ ∧ (8 : ℤ) ∣ c1 χ ↔ χ 2 = 1) ∧ (χ 2 = 1 ↔ ∃ y : ZMod p, y ^ 4 = 2) ∧
      c0 χ ≡ 4 * (R χ 1 + R χ 3) [ZMOD 8] ∧ c1 χ ≡ 4 * (R χ 1 + R χ 3) [ZMOD 8] := by sorry
