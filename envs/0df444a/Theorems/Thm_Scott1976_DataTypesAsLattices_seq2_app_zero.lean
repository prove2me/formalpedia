-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_seq2_app_zero
-- name    : Scott1976.DataTypesAsLattices.seq2_app_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:42.442514+00:00
-- url     : https://prove2.me/theorems/56108a7b-7aba-4c28-8196-21def4d37c56
-- title:
--   Data Types As Lattices: seq2 app zero
-- statement:
--   The Data Types As Lattices construction uses the seq2 app zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L580-L583
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L580-L583

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.seq2_app_zero (x y : Pomega) : funOf (seq2 x y) (ofNat 0) = x := by sorry
