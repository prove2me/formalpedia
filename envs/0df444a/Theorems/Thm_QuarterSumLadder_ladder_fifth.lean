-- Prove2me | Theorems.Thm_QuarterSumLadder_ladder_fifth
-- name    : QuarterSumLadder.ladder_fifth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:17:44.198623+00:00
-- url     : https://prove2.me/theorems/de2aac59-6b18-5df7-9662-31ffa3364e75
-- title:
--   Quarter Sum Ladder: ladder fifth
-- statement:
--   **The fifth threshold** (Paper IV, Theorem 5.6), with `h = 2N(Ω)` (`= h⁻(K)` by Proposition 4.1,
--   not formalized): `64 ∣ h ⟺ 32 ∣ h ∧ R₂ + R₃ ≡ Q/2 (mod 4)`; and given `32 ∣ h`,
--   `64 ∣ h ⟺ x + y ≡ 0 (mod 8)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L153-L158
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L153-L158

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.ladder_fifth {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    ((64 : ℤ) ∣ 2 * (Omega χ).norm ↔
        (32 : ℤ) ∣ 2 * (Omega χ).norm ∧ ((R χ 2 + R χ 3 : ℕ) : ℤ) % 4 = ((Q p / 2 : ℕ) : ℤ) % 4) ∧
      ((32 : ℤ) ∣ 2 * (Omega χ).norm →
        ((64 : ℤ) ∣ 2 * (Omega χ).norm ↔ (8 : ℤ) ∣ (Omega χ).re + (Omega χ).im)) := by sorry
