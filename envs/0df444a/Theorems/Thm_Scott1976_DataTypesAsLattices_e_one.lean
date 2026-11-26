-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_e_one
-- name    : Scott1976.DataTypesAsLattices.e_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:56:19.152112+00:00
-- url     : https://prove2.me/theorems/d037e00b-be11-5b9a-a78a-af3cb2dcbf5e
-- title:
--   Data Types As Lattices: e one
-- statement:
--   The Data Types As Lattices construction uses the e one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L88-L89
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L88-L89

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.e_one : e 1 = ({0} : Pomega) := by sorry
