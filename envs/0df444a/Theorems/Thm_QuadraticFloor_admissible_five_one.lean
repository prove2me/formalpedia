-- Prove2me | Theorems.Thm_QuadraticFloor_admissible_five_one
-- name    : QuadraticFloor.admissible_five_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:41.580466+00:00
-- url     : https://prove2.me/theorems/09ce19e3-86fa-548a-9582-2f2bdc9ac2a2
-- title:
--   Quadratic Floor: admissible five one
-- statement:
--   The Quadratic Floor construction uses the admissible five one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L183-L183
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L183-L183

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.admissible_five_one : Admissible 5 1 0 := by sorry
