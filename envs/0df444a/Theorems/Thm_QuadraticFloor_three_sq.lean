-- Prove2me | Theorems.Thm_QuadraticFloor_three_sq
-- name    : QuadraticFloor.three_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:13.421456+00:00
-- url     : https://prove2.me/theorems/a6d85df7-0c90-4836-9102-bbf71de7c4ce
-- title:
--   Quadratic Floor: three sq
-- statement:
--   The Quadratic Floor construction uses the three sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L113-L113
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L113-L113

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.three_sq : ((3 : ℤ) : ZMod 5) ^ 2 = 2 ^ 2 := by sorry
