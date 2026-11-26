-- Prove2me | Theorems.Thm_QuadraticFloor_ite_of_neg
-- name    : QuadraticFloor.ite_of_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:43:03.50755+00:00
-- url     : https://prove2.me/theorems/c32c5fc1-f778-59b9-8448-b403be224021
-- title:
--   Quadratic Floor: ite of neg
-- statement:
--   The Quadratic Floor construction uses the ite of neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Defs.lean#L36-L37
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Defs.lean#L36-L37

module
public import Mathlib
public import Definitions.Def_QuadraticFloor_Defs
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.ite_of_neg {α : Sort*} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by sorry
