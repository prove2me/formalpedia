-- Prove2me | Theorems.Thm_QuadraticFloor_osum_zero
-- name    : QuadraticFloor.osum_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:34.117707+00:00
-- url     : https://prove2.me/theorems/f9ac604b-fab9-442f-826e-9637c353eff6
-- title:
--   Quadratic Floor: osum zero
-- statement:
--   The Quadratic Floor construction uses the osum zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L34-L34
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L34-L34

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.osum_zero (g : ℤ → ℤ) : osum 0 g = 0 := by sorry
