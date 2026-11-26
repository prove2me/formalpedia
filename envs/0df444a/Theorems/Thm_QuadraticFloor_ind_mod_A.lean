-- Prove2me | Theorems.Thm_QuadraticFloor_ind_mod_A
-- name    : QuadraticFloor.ind_mod_A
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:15.178579+00:00
-- url     : https://prove2.me/theorems/d8a097c2-f5ea-4f41-812e-88f30138b781
-- title:
--   Quadratic Floor: ind mod A
-- statement:
--   Orthogonality modulo `A`: the indicator of `x ≡ d (mod A)`, with `d ≡ B²`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L70-L90
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L70-L90

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.ind_mod_A {A : ℕ} [NeZero A] {B : ℤ} (hB : Int.gcd B A = 1) {d : ℕ}
    (hd : (d : ZMod A) = (B : ZMod A) ^ 2) (x : ℕ) :
    (if x % A = d % A then (1 : ℂ) else 0) =
      (1 / (A.totient : ℂ)) *
        ∑ ψ : DirichletCharacter ℂ A, (starRingEnd ℂ (ψ (B : ZMod A))) ^ 2 * ψ (x : ZMod A) := by sorry
