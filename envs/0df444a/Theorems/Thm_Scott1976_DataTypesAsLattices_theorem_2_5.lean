-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_2_5
-- name    : Scott1976.DataTypesAsLattices.theorem_2_5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:19.672404+00:00
-- url     : https://prove2.me/theorems/b1060385-420a-4f7e-9e9a-36aa1cdd13ee
-- title:
--   Data Types As Lattices: theorem 2 5
-- statement:
--   **Scott 1976, Theorem 2.5 (The first recursion theorem).**
--   If `u` is the graph of a continuous `f`, then `Y(u) = fix(f)`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L499-L502
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L499-L502

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_2_5 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    funOf Ycomb (graph f) = fix f := by sorry
