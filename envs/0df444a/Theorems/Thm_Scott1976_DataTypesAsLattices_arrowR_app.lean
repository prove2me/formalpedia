-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_arrowR_app
-- name    : Scott1976.DataTypesAsLattices.arrowR_app
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:59.454059+00:00
-- url     : https://prove2.me/theorems/4d2254f1-c407-570e-9b47-dc934fec1620
-- title:
--   Data Types As Lattices: arrow R app
-- statement:
--   The Data Types As Lattices construction uses the arrow R app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L205-L207
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L205-L207

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.arrowR_app (a b u : Pomega) :
    funOf (arrowR a b) u = comp b (comp u a) := by sorry
