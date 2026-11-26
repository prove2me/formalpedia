-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_funOf_isScottContinuous
-- name    : Scott1976.DataTypesAsLattices.funOf_isScottContinuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:27.772709+00:00
-- url     : https://prove2.me/theorems/340eeea8-c326-488e-8d8b-8e2dd60bf288
-- title:
--   Data Types As Lattices: fun Of is Scott Continuous
-- statement:
--   The Data Types As Lattices construction uses the fun Of is Scott Continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L52-L60
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L52-L60

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.funOf_isScottContinuous (u : Pomega) : IsScottContinuous (funOf u) := by sorry
