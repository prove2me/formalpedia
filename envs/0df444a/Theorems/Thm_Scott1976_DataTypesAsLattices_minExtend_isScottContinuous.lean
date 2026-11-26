-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_minExtend_isScottContinuous
-- name    : Scott1976.DataTypesAsLattices.minExtend_isScottContinuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:30.194993+00:00
-- url     : https://prove2.me/theorems/d3fa79b6-f394-46b2-b3a7-2745cc25726d
-- title:
--   Data Types As Lattices: min Extend is Scott Continuous
-- statement:
--   The Data Types As Lattices construction uses the min Extend is Scott Continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L33-L45
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L33-L45

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.minExtend_isScottContinuous (p : ℕ → Pomega) :
    IsScottContinuous (minExtend p) := by sorry
