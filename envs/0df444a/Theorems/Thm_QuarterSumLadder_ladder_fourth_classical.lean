-- Prove2me | Theorems.Thm_QuarterSumLadder_ladder_fourth_classical
-- name    : QuarterSumLadder.ladder_fourth_classical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:17:54.450804+00:00
-- url     : https://prove2.me/theorems/a5552f0e-fb7d-473a-aa87-1236f518e3c7
-- title:
--   Quarter Sum Ladder: ladder fourth classical
-- statement:
--   **The classical evaluation of the fourth threshold** (Paper IV, Theorem 5.4): if `χ(2) = 1` and
--   `p ≡ 1 (mod 16)`, then `4 ∣ κ` and, with `ρ = ord_p(2)`,
--   `16 ∣ N(Ω) ⟺ (Q - κ)/4 + (p - 1)/8 + [2 ∣ ρ] (p - 1)/(4ρ) ≡ 0 (mod 2)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L125-L132
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L125-L132

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.ladder_fourth_classical {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) (hw : χ 2 = 1)
    (h16 : p % 16 = 1) :
    (4 : ℤ) ∣ kappa p ∧
      ((16 : ℤ) ∣ (Omega χ).norm ↔
        (((Q p : ℤ) - kappa p) / 4 + ((p - 1) / 8 : ℕ) +
          ((if 2 ∣ orderOf (2 : ZMod p) then (p - 1) / (4 * orderOf (2 : ZMod p)) else 0 : ℕ) :
            ℤ)) % 2 = 0) := by sorry
