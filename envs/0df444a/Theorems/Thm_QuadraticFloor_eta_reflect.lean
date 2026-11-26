-- Prove2me | Theorems.Thm_QuadraticFloor_eta_reflect
-- name    : QuadraticFloor.eta_reflect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:49:02.573896+00:00
-- url     : https://prove2.me/theorems/8308228d-923c-5fe0-a98e-74140b257c44
-- title:
--   Quadratic Floor: eta reflect
-- statement:
--   `η_p(q - x) = -η_p(x)` when `8p ∣ q` and `x ≤ q`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Eta.lean#L119-L135
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Eta.lean#L119-L135

module
public import Definitions.Def_QuadraticFloor_RootCount
public import Definitions.Def_QuadraticFloor_Eta
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.eta_reflect (hp2 : p ≠ 2) {q : ℕ} (hq : 8 * p ∣ q) {x : ℕ} (hx : x ≤ q) :
    eta p (q - x) = -eta p x := by sorry
