-- Prove2me | Theorems.Thm_QuadraticFloor_card_quadratic_eq
-- name    : QuadraticFloor.card_quadratic_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:43:47.359697+00:00
-- url     : https://prove2.me/theorems/2f912097-1351-469b-90dd-db09b7975d66
-- title:
--   Quadratic Floor: card quadratic eq
-- statement:
--   The number of solutions of `A x² + B x + C = y` in `ZMod p` is `1 + ((D + 4Ay)/p)`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/RootCount.lean#L90-L115
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/RootCount.lean#L90-L115

module
public import Definitions.Def_QuadraticFloor_Defs
public import Definitions.Def_QuadraticFloor_RootCount
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.card_quadratic_eq (hp2 : p ≠ 2) {A B C : ZMod p} (hA : A ≠ 0) (y : ZMod p) :
    ((univ.filter fun x : ZMod p => A * x ^ 2 + B * x + C = y).card : ℤ) =
      quadraticChar (ZMod p) (B ^ 2 - 4 * A * C + 4 * A * y) + 1 := by sorry
