-- Prove2me | Theorems.Thm_Research_sqDist_triPoint_zero
-- name    : Research.sqDist_triPoint_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:07:00.363576+00:00
-- url     : https://prove2.me/theorems/6419f658-8805-44a2-805e-a25ccd5ddda1
-- title:
--   Research: sq Dist tri Point zero
-- statement:
--   The coordinate quadratic form really is squared Euclidean distance from the origin.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/TriangularShells.lean#L147-L154
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/TriangularShells.lean#L147-L154

module
public import Definitions.Def_Research_Basic
public import Definitions.Def_Research_TriangularShells
set_option autoImplicit true
@[expose] public section
public section
open Research

theorem Research.sqDist_triPoint_zero (p : ℤ × ℤ) :
    sqDist (triPoint p) (0, 0) = (triNormSq p : ℝ) := by sorry
