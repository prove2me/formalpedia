-- Prove2me | Theorems.Thm_QuadraticFloor_eta_eq
-- name    : QuadraticFloor.eta_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:01:44.697699+00:00
-- url     : https://prove2.me/theorems/ff88e816-9030-5a65-a3f2-c59803ffa140
-- title:
--   Quadratic Floor: eta eq
-- statement:
--   **Equation (8) of Section 2.** `η_p(x) = κ_p(x) (x/p)`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L32-L33
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/Solution.lean#L32-L33

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.eta_eq (hp2 : p ≠ 2) (x : ℕ) : eta p x = kap p x * legendreSym p x := by sorry
