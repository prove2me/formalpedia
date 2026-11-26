-- Prove2me | Theorems.Thm_P2M_QuadraticFloor_eta_eq__74b5fa8b45c2
-- name    : P2M_QuadraticFloor_eta_eq__74b5fa8b45c2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:44:36.503655+00:00
-- url     : https://prove2.me/theorems/428c07ca-0c5c-4ae5-be0b-ca97f7ead340
-- title:
--   P2 M Quadratic Floor eta eq  74b5fa8b45c2: P2 M Quadratic Floor eta eq  74b5fa8b45c2
-- statement:
--   **Equation (8) of Section 2**: `η_p(x) = κ_p(x) (x/p)`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Eta.lean#L49-L89
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Eta.lean#L49-L89

module
public import Definitions.Def_QuadraticFloor_RootCount
public import Definitions.Def_QuadraticFloor_Eta
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem P2M_QuadraticFloor_eta_eq__74b5fa8b45c2 (hp2 : p ≠ 2) (x : ℕ) : eta p x = kap p x * legendreSym p x := by sorry

alias «QuadraticFloor».«eta_eq'» := P2M_QuadraticFloor_eta_eq__74b5fa8b45c2
