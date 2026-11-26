-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_condSet_isScottContinuous_mid
-- name    : Scott1976.DataTypesAsLattices.condSet_isScottContinuous_mid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:34.291977+00:00
-- url     : https://prove2.me/theorems/d7b5d697-faf3-5539-9557-cd4a0db2da81
-- title:
--   Data Types As Lattices: cond Set is Scott Continuous mid
-- statement:
--   The Data Types As Lattices construction uses the cond Set is Scott Continuous mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L110-L124
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L110-L124

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.condSet_isScottContinuous_mid (z y : Pomega) :
    IsScottContinuous (fun x => condSet z x y) := by sorry
