-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_comp_app
-- name    : Scott1976.DataTypesAsLattices.comp_app
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:59.056371+00:00
-- url     : https://prove2.me/theorems/b3706c50-c74e-5607-9cd3-af84becf4d10
-- title:
--   Data Types As Lattices: comp app
-- statement:
--   The Data Types As Lattices construction uses the comp app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L26-L28
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L26-L28

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.comp_app (u v x : Pomega) :
    funOf (comp u v) x = funOf u (funOf v x) := by sorry
