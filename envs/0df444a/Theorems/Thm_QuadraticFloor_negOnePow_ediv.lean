-- Prove2me | Theorems.Thm_QuadraticFloor_negOnePow_ediv
-- name    : QuadraticFloor.negOnePow_ediv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:43:51.545566+00:00
-- url     : https://prove2.me/theorems/9936d05e-4c76-4c0e-b562-9d193d01ef6a
-- title:
--   Quadratic Floor: neg One Pow ediv
-- statement:
--   The parity of the quotient of `v` by the odd prime `p` is the parity of `v - (v mod p)`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/RootCount.lean#L62-L73
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/RootCount.lean#L62-L73

module
public import Definitions.Def_QuadraticFloor_Defs
public import Definitions.Def_QuadraticFloor_RootCount
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.negOnePow_ediv (hp2 : p ≠ 2) (v C : ℤ) (hv : Even (v - C)) :
    ((v / (p : ℤ)).negOnePow : ℤ) = (C.negOnePow : ℤ) * ((v % (p : ℤ)).negOnePow : ℤ) := by sorry
