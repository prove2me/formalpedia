-- Prove2me | Theorems.Thm_QuadraticFloor_kap_one
-- name    : QuadraticFloor.kap_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:43.557309+00:00
-- url     : https://prove2.me/theorems/c109ab4b-a439-4f7b-9d56-34034bac8aa7
-- title:
--   Quadratic Floor: kap one
-- statement:
--   The Quadratic Floor construction uses the kap one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Eta.lean#L29-L29
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Eta.lean#L29-L29

module
public import Definitions.Def_QuadraticFloor_RootCount
public import Definitions.Def_QuadraticFloor_Eta
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.kap_one (p : ℕ) : kap p 1 = 1 := by sorry
