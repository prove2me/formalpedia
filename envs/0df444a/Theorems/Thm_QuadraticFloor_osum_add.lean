-- Prove2me | Theorems.Thm_QuadraticFloor_osum_add
-- name    : QuadraticFloor.osum_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:53:06.753852+00:00
-- url     : https://prove2.me/theorems/95e02b04-3144-5485-9c96-4203a738eaa1
-- title:
--   Quadratic Floor: osum add
-- statement:
--   The Quadratic Floor construction uses the osum add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L61-L62
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L61-L62

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

theorem QuadraticFloor.osum_add (t : ℤ) (g h : ℤ → ℤ) : osum t (fun j => g j + h j) = osum t g + osum t h := by sorry
