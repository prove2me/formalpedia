-- Prove2me | Theorems.Thm_Research_mem_triCoordsWithin_iff_of_le_nine
-- name    : Research.mem_triCoordsWithin_iff_of_le_nine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:43:21.406426+00:00
-- url     : https://prove2.me/theorems/4db01e18-781a-42b3-8c63-f411f50a1b88
-- title:
--   Research: mem tri Coords Within iff of le nine
-- statement:
--   Every census with squared-radius at most nine is complete, not merely a
--   count inside an arbitrarily chosen finite window.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/TriangularShells.lean#L63-L78
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/TriangularShells.lean#L63-L78

module
public import Definitions.Def_Research_Basic
public import Definitions.Def_Research_TriangularShells
set_option autoImplicit true
@[expose] public section
public section
open Research

theorem Research.mem_triCoordsWithin_iff_of_le_nine (s : ℤ) (hs : s ≤ 9)
    (p : ℤ × ℤ) :
    p ∈ triCoordsWithin s ↔ p ≠ (0, 0) ∧ triNormSq p ≤ s := by sorry
