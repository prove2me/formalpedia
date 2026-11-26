-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_eq_2_28
-- name    : Scott1976.DataTypesAsLattices.eq_2_28
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:47.674267+00:00
-- url     : https://prove2.me/theorems/a59ef7bb-6142-5704-98cd-b20343154b83
-- title:
--   Data Types As Lattices: eq 2 28
-- statement:
--   **Scott 1976, (2.28).** Least-fixed-point unfolding `Y(g(x)) = g(x)(Y(g(x)))`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L600-L603
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L600-L603

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.eq_2_28 {g : Pomega → Pomega → Pomega}
    (hgy : ∀ x, IsScottContinuous (fun y => g x y)) (x : Pomega) :
    fix (g x) = g x (fix (g x)) := by sorry
