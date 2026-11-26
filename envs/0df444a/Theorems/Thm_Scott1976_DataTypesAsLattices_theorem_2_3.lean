-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_2_3
-- name    : Scott1976.DataTypesAsLattices.theorem_2_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:09.677648+00:00
-- url     : https://prove2.me/theorems/a3473d35-ca75-59a2-813b-6e882b7ebeb4
-- title:
--   Data Types As Lattices: theorem 2 3
-- statement:
--   **Scott 1976, Theorem 2.3 (The reduction theorem), binary case.**
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L389-L393
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L389-L393

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_2_3 {f : Pomega → Pomega → Pomega}
    (hfx : ∀ y, IsScottContinuous (fun x => f x y))
    (hfy : ∀ x, IsScottContinuous (fun y => f x y)) :
    ∃ u, ∀ x y, funOf (funOf u x) y = f x y := by sorry
