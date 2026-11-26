-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_funOf_isScottContinuous_left
-- name    : Scott1976.DataTypesAsLattices.funOf_isScottContinuous_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:40.562935+00:00
-- url     : https://prove2.me/theorems/757c024e-6c06-4258-980e-175d65fce37f
-- title:
--   Data Types As Lattices: fun Of is Scott Continuous left
-- statement:
--   The Data Types As Lattices construction uses the fun Of is Scott Continuous left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L142-L153
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L142-L153

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.funOf_isScottContinuous_left (y : Pomega) :
    IsScottContinuous (fun u => funOf u y) := by sorry
