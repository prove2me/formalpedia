-- Prove2me | Theorems.Thm_Research_triCoordsWithin_nine_card
-- name    : Research.triCoordsWithin_nine_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:03:38.946105+00:00
-- url     : https://prove2.me/theorems/4fa88ebe-03fb-4ae8-8776-4153ff8c9d1b
-- title:
--   Research: tri Coords Within nine card
-- statement:
--   Exact enumeration through radius three.  The printed value 18 is not the
--   natural triangular-lattice ball count; the correct count is 36.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/TriangularShells.lean#L139-L140
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/TriangularShells.lean#L139-L140

module
public import Definitions.Def_Research_Basic
public import Definitions.Def_Research_TriangularShells
set_option autoImplicit true
@[expose] public section
public section
open Research

theorem Research.triCoordsWithin_nine_card : (triCoordsWithin 9).card = 36 := by sorry
