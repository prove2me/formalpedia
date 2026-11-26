-- Prove2me | Theorems.Thm_QuadraticFloor_bern_conj
-- name    : QuadraticFloor.bern_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:59.429662+00:00
-- url     : https://prove2.me/theorems/c82dd4ea-6709-5fd1-819e-5395031fb8e1
-- title:
--   Quadratic Floor: bern conj
-- statement:
--   The Quadratic Floor construction uses the bern conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L117-L123
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L117-L123

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.bern_conj (q : ℕ) (f : ℕ → ℂ) :
    bern q (fun x => starRingEnd ℂ (f x)) = starRingEnd ℂ (bern q f) := by sorry
