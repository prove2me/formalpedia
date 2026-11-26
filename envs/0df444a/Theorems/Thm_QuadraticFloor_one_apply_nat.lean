-- Prove2me | Theorems.Thm_QuadraticFloor_one_apply_nat
-- name    : QuadraticFloor.one_apply_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:40.065934+00:00
-- url     : https://prove2.me/theorems/9eec72cd-bc10-47bd-bd53-6c8748a339fb
-- title:
--   Quadratic Floor: one apply nat
-- statement:
--   The Quadratic Floor construction uses the one apply nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L143-L150
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L143-L150

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.one_apply_nat (x : ℕ) :
    (1 : DirichletCharacter ℂ 5) (x : ZMod 5) = if 5 ∣ x then 0 else 1 := by sorry
