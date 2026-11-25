-- Prove2me | Theorems.Thm_Research_triCoordsWithin_one_card
-- name    : Research.triCoordsWithin_one_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:43:27.301959+00:00
-- url     : https://prove2.me/theorems/84f86b42-5c77-4844-b256-867879f416c8
-- title:
--   Research: tri Coords Within one card
-- statement:
--   Exact enumeration of the first radius of the triangular lattice.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/TriangularShells.lean#L97-L98
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/TriangularShells.lean#L97-L98

module
public import Definitions.Def_Research_Basic
public import Definitions.Def_Research_TriangularShells
set_option autoImplicit true
@[expose] public section
public section
open Research

theorem Research.triCoordsWithin_one_card : (triCoordsWithin 1).card = 6 := by sorry
