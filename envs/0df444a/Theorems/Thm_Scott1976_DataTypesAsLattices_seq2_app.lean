-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_seq2_app
-- name    : Scott1976.DataTypesAsLattices.seq2_app
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:55:21.961949+00:00
-- url     : https://prove2.me/theorems/21b79244-d0a4-49e8-9034-e1f7781630b6
-- title:
--   Data Types As Lattices: seq2 app
-- statement:
--   The Data Types As Lattices construction uses the seq2 app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L576-L578
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L576-L578

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.seq2_app (x y z : Pomega) :
    funOf (seq2 x y) z = condSet z x (condSet (predSet z) y botElem) := by sorry
