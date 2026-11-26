-- Prove2me | Theorems.Thm_QuadraticFloor_I_ne_one
-- name    : QuadraticFloor.I_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:58:21.113891+00:00
-- url     : https://prove2.me/theorems/9f9625a9-cece-50a0-a835-a545ec35aac8
-- title:
--   Quadratic Floor: I ne one
-- statement:
--   The Quadratic Floor construction uses the I ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L83-L83
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L83-L83

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.I_ne_one : Complex.I ≠ 1 := by sorry
