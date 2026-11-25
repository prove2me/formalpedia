-- Prove2me | Theorems.Thm_Research_triCoordsWithinThirtySix_card
-- name    : Research.triCoordsWithinThirtySix_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:47:46.298803+00:00
-- url     : https://prove2.me/theorems/4ace2bb9-5ba7-4865-9e70-15532a5b6062
-- title:
--   Research: tri Coords Within Thirty Six card
-- statement:
--   Exact kernel census: the unit triangular lattice has 126 nonzero points at
--   ordinary distance at most six.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L154-L156
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L154-L156

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.triCoordsWithinThirtySix_card :
    triCoordsWithinThirtySix.card = 126 := by sorry
