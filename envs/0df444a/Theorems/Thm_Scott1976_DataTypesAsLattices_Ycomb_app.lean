-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_Ycomb_app
-- name    : Scott1976.DataTypesAsLattices.Ycomb_app
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:56:46.102485+00:00
-- url     : https://prove2.me/theorems/6c72adf8-4564-57c7-ab09-993abe77a7b2
-- title:
--   Data Types As Lattices: Ycomb app
-- statement:
--   The Data Types As Lattices construction uses the Ycomb app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L436-L438
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L436-L438

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.Ycomb_app (u : Pomega) :
    funOf Ycomb u = funOf (omegaComb u) (omegaComb u) := by sorry
