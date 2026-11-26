-- Prove2me | Theorems.Thm_QuadraticFloor_univ_char5
-- name    : QuadraticFloor.univ_char5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:48.567784+00:00
-- url     : https://prove2.me/theorems/4724af9a-1244-4888-b832-45869b8e972b
-- title:
--   Quadratic Floor: univ char5
-- statement:
--   The Quadratic Floor construction uses the univ char5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L73-L81
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L73-L81

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.univ_char5 :
    (univ : Finset (DirichletCharacter ℂ 5)) = {1, xi, xi * xi, star xi} := by sorry
