-- Prove2me | Theorems.Thm_QuarterSumLadder_weight_two_congruence
-- name    : QuarterSumLadder.weight_two_congruence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:08:52.504542+00:00
-- url     : https://prove2.me/theorems/ba49ba6b-df27-44d1-8600-bdda3d3ca910
-- title:
--   Quarter Sum Ladder: weight two congruence
-- statement:
--   **The weight-two congruence** (Paper IV, Theorem 3.1 at order `4`).
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L146-L193
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L146-L193

module
public import Definitions.Def_QuarterSumLadder_Counts
public import Definitions.Def_QuarterSumLadder_WeightTwo
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ

theorem QuarterSumLadder.weight_two_congruence :
    c0 χ ≡ 4 * (E χ 1 + E χ (-1)) [ZMOD 8] ∧ c1 χ ≡ 4 * (E χ gi + E χ (-gi)) [ZMOD 8] ∧
      c0 χ + c1 χ ≡ p - 1 [ZMOD 8] := by sorry
