-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_arrowR_map_isScottContinuous
-- name    : Scott1976.DataTypesAsLattices.arrowR_map_isScottContinuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:57:16.157718+00:00
-- url     : https://prove2.me/theorems/492bba35-55ed-421a-8b35-a8a270c7222b
-- title:
--   Data Types As Lattices: arrow R map is Scott Continuous
-- statement:
--   The Data Types As Lattices construction uses the arrow R map is Scott Continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L201-L203
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L201-L203

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.arrowR_map_isScottContinuous (a b : Pomega) :
    IsScottContinuous (fun u => comp b (comp u a)) := by sorry
