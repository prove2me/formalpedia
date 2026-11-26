-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_graph_const_isScottContinuous
-- name    : Scott1976.DataTypesAsLattices.graph_const_isScottContinuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:35.724476+00:00
-- url     : https://prove2.me/theorems/2d5deba7-3068-4848-ae2c-34f8fa245322
-- title:
--   Data Types As Lattices: graph const is Scott Continuous
-- statement:
--   `graph (fun y => g x y)` is continuous in `x` when `g` is continuous in `x`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L196-L211
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L196-L211

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.graph_const_isScottContinuous
    (g : Pomega → Pomega → Pomega)
    (hg : ∀ y, IsScottContinuous (fun x => g x y)) :
    IsScottContinuous (fun x => graph (fun y => g x y)) := by sorry
