-- Prove2me | Theorems.Thm_QuadraticFloor_char_inv_eq_star
-- name    : QuadraticFloor.char_inv_eq_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:49:54.224101+00:00
-- url     : https://prove2.me/theorems/a460918f-5c19-5535-82db-c6d0dc8a949a
-- title:
--   Quadratic Floor: char inv eq star
-- statement:
--   The Quadratic Floor construction uses the char inv eq star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L51-L58
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/SquareClass.lean#L51-L58

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.char_inv_eq_star {A : ℕ} [NeZero A] (ψ : DirichletCharacter ℂ A) {a : ZMod A}
    (ha : IsUnit a) : ψ a⁻¹ = star (ψ a) := by sorry
