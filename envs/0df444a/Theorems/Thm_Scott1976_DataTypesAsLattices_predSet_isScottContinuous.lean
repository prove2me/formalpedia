-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_predSet_isScottContinuous
-- name    : Scott1976.DataTypesAsLattices.predSet_isScottContinuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:47.243127+00:00
-- url     : https://prove2.me/theorems/3a6d6668-a455-4488-9036-217e8e65a3c9
-- title:
--   Data Types As Lattices: pred Set is Scott Continuous
-- statement:
--   The Data Types As Lattices construction uses the pred Set is Scott Continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L76-L86
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L76-L86

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.predSet_isScottContinuous : IsScottContinuous predSet := by sorry
