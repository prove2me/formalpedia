-- Prove2me | Theorems.Thm_QuarterSumLadder_coord_parity
-- name    : QuarterSumLadder.coord_parity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:10:04.654435+00:00
-- url     : https://prove2.me/theorems/4ea27a4e-32a0-4f05-8f8a-7ea1b6c1f468
-- title:
--   Quarter Sum Ladder: coord parity
-- statement:
--   The parities of the coordinates.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Ladder.lean#L48-L66
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Ladder.lean#L48-L66

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

theorem QuarterSumLadder.coord_parity :
    (χ 2 = -1 → (Omega χ).re % 2 = 1 ∧ (Omega χ).im % 2 = 1) ∧
      (χ 2 = 1 → (Omega χ).re % 2 = 0 ∧ (Omega χ).im % 2 = 0 ∧
        ((Omega χ).re - (Omega χ).im) % 4 = (Q p : ℤ) % 4) := by sorry
