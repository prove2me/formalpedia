-- Prove2me | Theorems.Thm_QuadraticFloor_xi_four
-- name    : QuadraticFloor.xi_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:37.154083+00:00
-- url     : https://prove2.me/theorems/d00ecb07-cc2f-4b13-a2a1-8db656baae80
-- title:
--   Quadratic Floor: xi four
-- statement:
--   The Quadratic Floor construction uses the xi four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L35-L38
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L35-L38

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.xi_four : xi 4 = -1 := by sorry
