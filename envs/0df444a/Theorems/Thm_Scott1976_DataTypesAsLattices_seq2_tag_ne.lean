-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_seq2_tag_ne
-- name    : Scott1976.DataTypesAsLattices.seq2_tag_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:56:53.63955+00:00
-- url     : https://prove2.me/theorems/cc7b67b0-f66e-4936-91bf-cef137d9da0b
-- title:
--   Data Types As Lattices: seq2 tag ne
-- statement:
--   The Data Types As Lattices construction uses the seq2 tag ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L590-L597
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L590-L597

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.seq2_tag_ne (x y : Pomega) :
    seq2 (ofNat 0) x ≠ seq2 (ofNat 1) y := by sorry
