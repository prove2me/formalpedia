-- Prove2me | Theorems.Thm_QuadraticFloor_negOnePow_emod
-- name    : QuadraticFloor.negOnePow_emod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:44:53.337371+00:00
-- url     : https://prove2.me/theorems/5fde6327-9ad0-46cb-a3bf-c1dd5b1ca7a3
-- title:
--   Quadratic Floor: neg One Pow emod
-- statement:
--   `(-1)^{x mod p}` written through the least residue in `ZMod p`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/RootCount.lean#L85-L87
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/RootCount.lean#L85-L87

module
public import Definitions.Def_QuadraticFloor_Defs
public import Definitions.Def_QuadraticFloor_RootCount
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.negOnePow_emod (v : ℤ) :
    ((v % (p : ℤ)).negOnePow : ℤ) = (-1) ^ ((v : ZMod p).val) := by sorry
