-- Prove2me | Theorems.Thm_QuadraticFloor_kap_neg_one_mul_legendre
-- name    : QuadraticFloor.kap_neg_one_mul_legendre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:52.045224+00:00
-- url     : https://prove2.me/theorems/05516d7d-124a-51bf-81e4-6e20bfe63d83
-- title:
--   Quadratic Floor: kap neg one mul legendre
-- statement:
--   `κ_p(-1) (-1/p) = -1`: `η_p` is odd.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Eta.lean#L39-L46
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Eta.lean#L39-L46

module
public import Definitions.Def_QuadraticFloor_RootCount
public import Definitions.Def_QuadraticFloor_Eta
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.kap_neg_one_mul_legendre (hp2 : p ≠ 2) : kap p (-1) * legendreSym p (-1) = -1 := by sorry
