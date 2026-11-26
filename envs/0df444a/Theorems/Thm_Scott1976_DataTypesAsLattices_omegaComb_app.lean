-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_omegaComb_app
-- name    : Scott1976.DataTypesAsLattices.omegaComb_app
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:56:41.753449+00:00
-- url     : https://prove2.me/theorems/200e2215-62d7-4793-8102-f9dbc30c09da
-- title:
--   Data Types As Lattices: omega Comb app
-- statement:
--   The Data Types As Lattices construction uses the omega Comb app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L432-L434
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L432-L434

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.omegaComb_app (u x : Pomega) :
    funOf (omegaComb u) x = funOf u (funOf x x) := by sorry
