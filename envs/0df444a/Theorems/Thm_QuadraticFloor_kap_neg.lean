-- Prove2me | Theorems.Thm_QuadraticFloor_kap_neg
-- name    : QuadraticFloor.kap_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:56.108048+00:00
-- url     : https://prove2.me/theorems/5bfd8a22-7ac6-45d1-ad8e-c73e47fec178
-- title:
--   Quadratic Floor: kap neg
-- statement:
--   The Quadratic Floor construction uses the kap neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Eta.lean#L33-L34
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Eta.lean#L33-L34

module
public import Definitions.Def_QuadraticFloor_RootCount
public import Definitions.Def_QuadraticFloor_Eta
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.kap_neg (p : ℕ) (y : ZMod 8) : kap p (-y) = kap p (-1) * kap p y := by sorry
