-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_3_diag
-- name    : Scott1976.DataTypesAsLattices.theorem_1_3_diag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:45.224398+00:00
-- url     : https://prove2.me/theorems/94dc6ba1-95fe-43b1-a813-f4901f345d4c
-- title:
--   Data Types As Lattices: theorem 1 3 diag
-- statement:
--   **Scott 1976, Theorem 1.3 (The substitution theorem), binary case.**
--   If `f` is continuous in each argument separately, then `x ↦ f(x,x)` is
--   continuous.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/FixedPoint.lean#L17-L39
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/FixedPoint.lean#L17-L39

import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_1_3_diag {f : Pomega → Pomega → Pomega}
    (hfx : ∀ y, IsScottContinuous (fun x => f x y))
    (hfy : ∀ x, IsScottContinuous (fun y => f x y))
    {x : Pomega} :
    f x x = ⋃ n, {k | e n ⊆ x ∧ k ∈ f (e n) (e n)} := by sorry
