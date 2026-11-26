-- Prove2me | Theorems.Thm_QuarterSumLadder_quarter_interval_formula
-- name    : QuarterSumLadder.quarter_interval_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:17:30.839797+00:00
-- url     : https://prove2.me/theorems/43543b62-0fb2-4b2e-97ad-604fc49b41a7
-- title:
--   Quarter Sum Ladder: quarter interval formula
-- statement:
--   **The quarter-interval formula** in counting form (after Theorem 3.2): `κ = ∑_{0<n<p/4} (n/p)`
--   equals `Q - 2(R₁ + R₃)`, and `χ(2) = 1 ⟺ κ ≡ Q (mod 4)`. With `h(-4p) = 2κ` (Dirichlet's class
--   number formula, not formalized) this is `w = 1 ⟺ h(-4p) ≡ (p - 1)/2 (mod 8)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L75-L77
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L75-L77

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.quarter_interval_formula {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    kappa p = (Q p : ℤ) - 2 * (R χ 1 + R χ 3) ∧ (χ 2 = 1 ↔ kappa p % 4 = (Q p : ℤ) % 4) := by sorry
