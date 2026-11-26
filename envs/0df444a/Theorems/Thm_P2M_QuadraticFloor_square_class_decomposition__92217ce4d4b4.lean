-- Prove2me | Theorems.Thm_P2M_QuadraticFloor_square_class_decomposition__92217ce4d4b4
-- name    : P2M_QuadraticFloor_square_class_decomposition__92217ce4d4b4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:45:58.976537+00:00
-- url     : https://prove2.me/theorems/d75fdcd2-5b78-4f9c-9bb2-aa7eb733be10
-- title:
--   P2 M Quadratic Floor square class decomposition  92217ce4d4b4: P2 M Quadratic Floor square class decomposition  92217ce4d4b4
-- statement:
--   **Theorem 3.2 (square-class decomposition).**
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L368-L432
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L368-L432

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

theorem P2M_QuadraticFloor_square_class_decomposition__92217ce4d4b4 (hp2 : p ≠ 2) [NeZero A] (hA : Odd A) (hpA : ¬ p ∣ A)
    {B C : ℤ} (hBC : Admissible A B C) :
    (floorSum A B C p : ℂ) = (C.negOnePow : ℤ) - (1 / (A.totient : ℂ)) *
      ∑ ψ : DirichletCharacter ℂ A, (starRingEnd ℂ (ψ (B : ZMod A))) ^ 2 *
        bern (8 * A * p) (vartheta p ψ) := by sorry

alias «QuadraticFloor».«square_class_decomposition'» := P2M_QuadraticFloor_square_class_decomposition__92217ce4d4b4
