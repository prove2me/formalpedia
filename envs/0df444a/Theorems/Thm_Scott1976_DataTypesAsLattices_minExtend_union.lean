-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_minExtend_union
-- name    : Scott1976.DataTypesAsLattices.minExtend_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:30.006261+00:00
-- url     : https://prove2.me/theorems/45b86fda-30f9-44ce-a2bc-04c8d6d68fbf
-- title:
--   Data Types As Lattices: min Extend union
-- statement:
--   The Data Types As Lattices construction uses the min Extend union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L25-L28
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L25-L28

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.minExtend_union (p : ℕ → Pomega) (x y : Pomega) :
    minExtend p (x ∪ y) = minExtend p x ∪ minExtend p y := by sorry
