-- Prove2me | Theorems.Thm_Research_mem_triCoordsWithin_nine_iff
-- name    : Research.mem_triCoordsWithin_nine_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:43:32.969799+00:00
-- url     : https://prove2.me/theorems/548d0de7-4410-4d8c-b1ed-e576f759ab7a
-- title:
--   Research: mem tri Coords Within nine iff
-- statement:
--   The radius-three instance of census completeness.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/TriangularShells.lean#L81-L94
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/TriangularShells.lean#L81-L94

module
public import Definitions.Def_Research_Basic
public import Definitions.Def_Research_TriangularShells
set_option autoImplicit true
@[expose] public section
public section
open Research

theorem Research.mem_triCoordsWithin_nine_iff (p : ℤ × ℤ) :
    p ∈ triCoordsWithin 9 ↔ p ≠ (0, 0) ∧ triNormSq p ≤ 9 := by sorry
