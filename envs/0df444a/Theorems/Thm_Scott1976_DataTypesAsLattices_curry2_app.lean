-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_curry2_app
-- name    : Scott1976.DataTypesAsLattices.curry2_app
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:56:36.329869+00:00
-- url     : https://prove2.me/theorems/e19f6fe0-2afa-507d-b056-330fde5edf98
-- title:
--   Data Types As Lattices: curry2 app
-- statement:
--   The Data Types As Lattices construction uses the curry2 app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L379-L386
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L379-L386

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.curry2_app (f : Pomega → Pomega → Pomega)
    (hfx : ∀ y, IsScottContinuous (fun x => f x y))
    (hfy : ∀ x, IsScottContinuous (fun y => f x y)) (x y : Pomega) :
    funOf (funOf (curry2 f hfx hfy) x) y = f x y := by sorry
