-- Prove2me | Theorems.Thm_QuarterSumLadder_ladder_bottom_valuation
-- name    : QuarterSumLadder.ladder_bottom_valuation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:17:24.480881+00:00
-- url     : https://prove2.me/theorems/f3ff39ea-af6c-5319-99a0-cd2927c9cbec
-- title:
--   Quarter Sum Ladder: ladder bottom valuation
-- statement:
--   **The first three thresholds** (Paper IV, Theorem 5.2) for `v_λ(Ω) = v₂(N(Ω))`: `1`, `2`, and `≥ 3`
--   (the last for `Ω ≠ 0`).
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L110-L113
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L110-L113

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.ladder_bottom_valuation {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    (χ 2 = -1 → vlam (Omega χ) = 1) ∧ (χ 2 = 1 → p % 16 = 9 → vlam (Omega χ) = 2) ∧
      (χ 2 = 1 → p % 16 = 1 → Omega χ ≠ 0 → 3 ≤ vlam (Omega χ)) := by sorry
