-- Prove2me | Theorems.Thm_QuadraticFloor_weight
-- name    : QuadraticFloor.weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:41.561957+00:00
-- url     : https://prove2.me/theorems/258faf9b-afb9-5466-9003-ef12792c0e73
-- title:
--   Quadratic Floor: weight
-- statement:
--   The Quadratic Floor construction uses the weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L109-L111
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L109-L111

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.weight (ψ : DirichletCharacter ℂ 5) (B : ℤ) :
    (starRingEnd ℂ (ψ (B : ZMod 5))) ^ 2 = starRingEnd ℂ (ψ ((B : ZMod 5) ^ 2)) := by sorry
