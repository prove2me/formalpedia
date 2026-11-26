-- Prove2me | Theorems.Thm_QuadraticFloor_kap_add_four
-- name    : QuadraticFloor.kap_add_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:30.032573+00:00
-- url     : https://prove2.me/theorems/e6feb779-16cb-4062-b2ef-cd7efb890f8a
-- title:
--   Quadratic Floor: kap add four
-- statement:
--   The Quadratic Floor construction uses the kap add four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Eta.lean#L23-L27
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Eta.lean#L23-L27

module
public import Definitions.Def_QuadraticFloor_RootCount
public import Definitions.Def_QuadraticFloor_Eta
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.kap_add_four (p : ℕ) (y : ZMod 8) : kap p (y + 4) = -kap p y := by sorry
