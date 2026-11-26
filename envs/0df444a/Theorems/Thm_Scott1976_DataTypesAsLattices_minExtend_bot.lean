-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_minExtend_bot
-- name    : Scott1976.DataTypesAsLattices.minExtend_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:26.625936+00:00
-- url     : https://prove2.me/theorems/0a83e427-2065-57a6-be09-aec29d4b9e28
-- title:
--   Data Types As Lattices: min Extend bot
-- statement:
--   The Data Types As Lattices construction uses the min Extend bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L30-L31
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L30-L31

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.minExtend_bot (p : ℕ → Pomega) : minExtend p botElem = botElem := by sorry
