-- Prove2me | Theorems.Thm_QuadraticFloor_one_two
-- name    : QuadraticFloor.one_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:23.47717+00:00
-- url     : https://prove2.me/theorems/7c6406bc-a66f-4c4c-8756-d63377cd8d78
-- title:
--   Quadratic Floor: one two
-- statement:
--   The Quadratic Floor construction uses the one two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L64-L65
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L64-L65

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.one_two : (1 : DirichletCharacter ℂ 5) 2 = 1 := by sorry
