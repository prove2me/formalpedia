-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_retract_app
-- name    : Scott1976.DataTypesAsLattices.retract_app
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:55:29.983005+00:00
-- url     : https://prove2.me/theorems/ed8ee26d-77e7-4e4d-aeff-fb07779c4d0f
-- title:
--   Data Types As Lattices: retract app
-- statement:
--   The Data Types As Lattices construction uses the retract app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L191-L194
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L191-L194

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.retract_app {a : Pomega} (ha : IsRetract a) (x : Pomega) :
    funOf a (funOf a x) = funOf a x := by sorry
