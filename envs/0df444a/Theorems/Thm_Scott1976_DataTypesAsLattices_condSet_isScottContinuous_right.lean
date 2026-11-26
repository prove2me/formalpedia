-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_condSet_isScottContinuous_right
-- name    : Scott1976.DataTypesAsLattices.condSet_isScottContinuous_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:56:25.084847+00:00
-- url     : https://prove2.me/theorems/dac22ced-1583-4d3c-acc5-fb6738dcb2bc
-- title:
--   Data Types As Lattices: cond Set is Scott Continuous right
-- statement:
--   The Data Types As Lattices construction uses the cond Set is Scott Continuous right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L126-L140
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L126-L140

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.condSet_isScottContinuous_right (z x : Pomega) :
    IsScottContinuous (fun y => condSet z x y) := by sorry
