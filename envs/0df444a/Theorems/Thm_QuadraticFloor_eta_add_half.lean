-- Prove2me | Theorems.Thm_QuadraticFloor_eta_add_half
-- name    : QuadraticFloor.eta_add_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:44:42.25132+00:00
-- url     : https://prove2.me/theorems/1af45aa1-e9d0-4378-828b-9db81aef2771
-- title:
--   Quadratic Floor: eta add half
-- statement:
--   `η_p(x + 4Ap) = -η_p(x)` for odd `A`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Eta.lean#L99-L116
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Eta.lean#L99-L116

module
public import Definitions.Def_QuadraticFloor_RootCount
public import Definitions.Def_QuadraticFloor_Eta
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.eta_add_half (hp2 : p ≠ 2) {A : ℕ} (hA : Odd A) (x : ℕ) :
    eta p (x + 4 * A * p) = -eta p x := by sorry
