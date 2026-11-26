-- Prove2me | Theorems.Thm_QuarterSumLadder_kappa_eq
-- name    : QuarterSumLadder.kappa_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:07:00.80546+00:00
-- url     : https://prove2.me/theorems/e7febac1-bf5e-47ff-8cb6-d3e64a0777bd
-- title:
--   Quarter Sum Ladder: kappa eq
-- statement:
--   **The quarter-interval formula**: `κ = Q - 2(R₁ + R₃)`, where `κ = ∑_{0<n<p/4} (n/p)`
--   (which is `h(-4p)/2`).
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L332-L375
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L332-L375

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ

theorem QuarterSumLadder.kappa_eq : kappa p = (Q p : ℤ) - 2 * (R χ 1 + R χ 3) := by sorry
