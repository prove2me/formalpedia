-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_diagApp_isScottContinuous
-- name    : Scott1976.DataTypesAsLattices.diagApp_isScottContinuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:50.524218+00:00
-- url     : https://prove2.me/theorems/ef8c5f4b-b372-456e-a719-143fd5562b5b
-- title:
--   Data Types As Lattices: diag App is Scott Continuous
-- statement:
--   The Data Types As Lattices construction uses the diag App is Scott Continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L155-L171
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L155-L171

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.diagApp_isScottContinuous : IsScottContinuous (fun x => funOf x x) := by sorry
