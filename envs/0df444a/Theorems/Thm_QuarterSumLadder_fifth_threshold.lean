-- Prove2me | Theorems.Thm_QuarterSumLadder_fifth_threshold
-- name    : QuarterSumLadder.fifth_threshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:11:31.609508+00:00
-- url     : https://prove2.me/theorems/d117bc7b-b978-55d2-a3cb-8d018682d9f8
-- title:
--   Quarter Sum Ladder: fifth threshold
-- statement:
--   **The fifth threshold** (Paper IV, Theorem 5.6), with `h = 2 N(Ω)` (`= h⁻(K)`): `64 ∣ h` iff
--   `32 ∣ h` and `R₂ + R₃ ≡ Q/2 (mod 4)`; and, given `32 ∣ h`, `64 ∣ h ⟺ x + y ≡ 0 (mod 8)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Ladder.lean#L141-L171
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Ladder.lean#L141-L171

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

theorem QuarterSumLadder.fifth_threshold :
    ((64 : ℤ) ∣ 2 * (Omega χ).norm ↔
        (32 : ℤ) ∣ 2 * (Omega χ).norm ∧ ((R χ 2 + R χ 3 : ℕ) : ℤ) % 4 = ((Q p / 2 : ℕ) : ℤ) % 4) ∧
      ((32 : ℤ) ∣ 2 * (Omega χ).norm →
        ((64 : ℤ) ∣ 2 * (Omega χ).norm ↔ (8 : ℤ) ∣ (Omega χ).re + (Omega χ).im)) := by sorry
