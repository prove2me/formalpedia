-- Prove2me | Theorems.Thm_QuadraticFloor_sum_quadraticChar_affine
-- name    : QuadraticFloor.sum_quadraticChar_affine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:44:04.292325+00:00
-- url     : https://prove2.me/theorems/9efbe6dc-cd61-4b88-8da2-00c13825308f
-- title:
--   Quadratic Floor: sum quadratic Char affine
-- statement:
--   The complete sum of the quadratic character along an arithmetic progression vanishes.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/RootCount.lean#L118-L128
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/RootCount.lean#L118-L128

module
public import Definitions.Def_QuadraticFloor_Defs
public import Definitions.Def_QuadraticFloor_RootCount
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.sum_quadraticChar_affine (hp2 : p ≠ 2) {a : ZMod p} (ha : a ≠ 0) (b : ZMod p) :
    ∑ y : ZMod p, quadraticChar (ZMod p) (b + a * y) = 0 := by sorry
