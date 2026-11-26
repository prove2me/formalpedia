-- Prove2me | Theorems.Thm_QuadraticFloor_sum_window_char
-- name    : QuadraticFloor.sum_window_char
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:02.926055+00:00
-- url     : https://prove2.me/theorems/1647b4b8-a7d6-4dcd-9931-232b47a555ae
-- title:
--   Quadratic Floor: sum window char
-- statement:
--   The windowed character sum for one `ψ` is the half sum of `ϑ_{p,ψ}`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L304-L356
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L304-L356

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

theorem QuadraticFloor.sum_window_char (hp2 : p ≠ 2) (hA : Odd A) (hpA : ¬ p ∣ A) (ψ : DirichletCharacter ℂ A)
    (k : ℂ) :
    ∑ x ∈ Icc 1 (4 * A * p), (eta p x : ℂ) * ψ (x : ZMod A) *
      (1 + (ZMod.χ₄ (x : ZMod 4) : ℂ) + k * ((ZMod.χ₈ (x : ZMod 8) : ℂ) + (ZMod.χ₈' (x : ZMod 8) : ℂ)))
      = ∑ x ∈ Icc 1 (4 * A * p), vartheta p ψ x := by sorry
