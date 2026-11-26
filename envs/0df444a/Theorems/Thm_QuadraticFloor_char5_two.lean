-- Prove2me | Theorems.Thm_QuadraticFloor_char5_two
-- name    : QuadraticFloor.char5_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:33.578802+00:00
-- url     : https://prove2.me/theorems/2266f09d-c98f-5d74-87a0-ca59bfb95d26
-- title:
--   Quadratic Floor: char5 two
-- statement:
--   The Quadratic Floor construction uses the char5 two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L49-L62
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L49-L62

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.char5_two (ψ : DirichletCharacter ℂ 5) :
    ψ 2 = 1 ∨ ψ 2 = Complex.I ∨ ψ 2 = -1 ∨ ψ 2 = -Complex.I := by sorry
