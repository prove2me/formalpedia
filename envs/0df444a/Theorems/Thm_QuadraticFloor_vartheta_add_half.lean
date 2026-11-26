-- Prove2me | Theorems.Thm_QuadraticFloor_vartheta_add_half
-- name    : QuadraticFloor.vartheta_add_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:00.962457+00:00
-- url     : https://prove2.me/theorems/b0a50336-0462-5835-83d1-470fb000919c
-- title:
--   Quadratic Floor: vartheta add half
-- statement:
--   `ϑ_{p,ψ}` changes sign under `x ↦ x + 4Ap`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L359-L363
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L359-L363

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {A : ℕ}

theorem QuadraticFloor.vartheta_add_half (hp2 : p ≠ 2) (hA : Odd A) (ψ : DirichletCharacter ℂ A) (x : ℕ) :
    vartheta p ψ (x + 4 * A * p) = -vartheta p ψ x := by sorry
