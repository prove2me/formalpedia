-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_condSet_isScottContinuous_left
-- name    : Scott1976.DataTypesAsLattices.condSet_isScottContinuous_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:56:29.478948+00:00
-- url     : https://prove2.me/theorems/c9962f41-0b0f-404b-bc66-103ac077cd51
-- title:
--   Data Types As Lattices: cond Set is Scott Continuous left
-- statement:
--   The Data Types As Lattices construction uses the cond Set is Scott Continuous left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L91-L108
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L91-L108

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.condSet_isScottContinuous_left (x y : Pomega) :
    IsScottContinuous (fun z => condSet z x y) := by sorry
