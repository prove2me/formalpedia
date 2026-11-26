-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_seq2_body_isScottContinuous
-- name    : Scott1976.DataTypesAsLattices.seq2_body_isScottContinuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:56:58.629876+00:00
-- url     : https://prove2.me/theorems/b416975f-43b4-46cd-bb6a-e6b946853026
-- title:
--   Data Types As Lattices: seq2 body is Scott Continuous
-- statement:
--   The Data Types As Lattices construction uses the seq2 body is Scott Continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L551-L574
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L551-L574

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.seq2_body_isScottContinuous (x y : Pomega) :
    IsScottContinuous (fun z => condSet z x (condSet (predSet z) y botElem)) := by sorry
