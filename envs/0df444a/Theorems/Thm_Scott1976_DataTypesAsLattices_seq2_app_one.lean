-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_seq2_app_one
-- name    : Scott1976.DataTypesAsLattices.seq2_app_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:55:12.202355+00:00
-- url     : https://prove2.me/theorems/386e690e-4920-51ee-a310-e7ac7b7d6295
-- title:
--   Data Types As Lattices: seq2 app one
-- statement:
--   The Data Types As Lattices construction uses the seq2 app one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L585-L588
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L585-L588

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.seq2_app_one (x y : Pomega) : funOf (seq2 x y) (ofNat 1) = y := by sorry
