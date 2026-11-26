-- Prove2me | Theorems.Thm_QuarterSumLadder_fourth_threshold_eval
-- name    : QuarterSumLadder.fourth_threshold_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:11:10.153603+00:00
-- url     : https://prove2.me/theorems/1360c486-d80c-57c2-9779-80239c3c5117
-- title:
--   Quarter Sum Ladder: fourth threshold eval
-- statement:
--   **The classical evaluation of the fourth threshold** (Paper IV, Theorem 5.4). If `χ(2) = 1`
--   and `p ≡ 1 (mod 16)`, then `4 ∣ κ` (that is, `8 ∣ h(-4p)`), and with `ρ = ord_p(2)`,
--   `16 ∣ N(Ω) ⟺ (Q - κ)/4 + (p - 1)/8 + [2 ∣ ρ] (p - 1)/(4ρ) ≡ 0 (mod 2)`. Here
--   `(Q - κ)/4 = (p - 1 - 2h(-4p))/16`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Ladder.lean#L109-L137
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Ladder.lean#L109-L137

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

theorem QuarterSumLadder.fourth_threshold_eval (hw : χ 2 = 1) (h16 : p % 16 = 1) :
    (4 : ℤ) ∣ kappa p ∧
      ((16 : ℤ) ∣ (Omega χ).norm ↔
        (((Q p : ℤ) - kappa p) / 4 + ((p - 1) / 8 : ℕ) +
          ((if 2 ∣ orderOf (2 : ZMod p) then (p - 1) / (4 * orderOf (2 : ZMod p)) else 0 : ℕ) :
            ℤ)) % 2 = 0) := by sorry
