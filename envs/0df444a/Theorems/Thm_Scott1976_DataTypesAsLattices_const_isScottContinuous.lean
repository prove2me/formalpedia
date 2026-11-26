-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_const_isScottContinuous
-- name    : Scott1976.DataTypesAsLattices.const_isScottContinuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:56:25.186173+00:00
-- url     : https://prove2.me/theorems/e13d71c5-8093-53f2-a5a7-bc95557c10cf
-- title:
--   Data Types As Lattices: const is Scott Continuous
-- statement:
--   The Data Types As Lattices construction uses the const is Scott Continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L184-L193
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L184-L193

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.const_isScottContinuous (c : Pomega) :
    IsScottContinuous (fun _ : Pomega => c) := by sorry
