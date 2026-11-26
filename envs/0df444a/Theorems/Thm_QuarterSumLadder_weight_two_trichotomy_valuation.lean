-- Prove2me | Theorems.Thm_QuarterSumLadder_weight_two_trichotomy_valuation
-- name    : QuarterSumLadder.weight_two_trichotomy_valuation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:17:51.023794+00:00
-- url     : https://prove2.me/theorems/8bf57cc0-acce-56b6-a833-903052b1120f
-- title:
--   Quarter Sum Ladder: weight two trichotomy valuation
-- statement:
--   **The weight-two trichotomy** (Paper IV, Theorem 8.2) for `v_λ(B_{2,χ})`: `5`, `6`, and `≥ 7`
--   (the last for `B_{2,χ} ≠ 0`).
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L176-L179
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L176-L179

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.weight_two_trichotomy_valuation {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    (χ 2 = -1 → vlam (B2 χ) = 5) ∧ (χ 2 = 1 → p % 16 = 9 → vlam (B2 χ) = 6) ∧
      (χ 2 = 1 → p % 16 = 1 → B2 χ ≠ 0 → 7 ≤ vlam (B2 χ)) := by sorry
