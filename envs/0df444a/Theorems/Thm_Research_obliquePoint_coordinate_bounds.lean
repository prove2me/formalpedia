-- Prove2me | Theorems.Thm_Research_obliquePoint_coordinate_bounds
-- name    : Research.obliquePoint_coordinate_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:02:06.228258+00:00
-- url     : https://prove2.me/theorems/ba320bab-d3dd-49bc-a189-891675a5c258
-- title:
--   Research: oblique Point coordinate bounds
-- statement:
--   Coarse exact coordinate bounds for separating translated copies.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L632-L650
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L632-L650

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.obliquePoint_coordinate_bounds (q : Fin 365 × Fin 365) :
    0 ≤ (obliquePoint q).1 ∧ (obliquePoint q).1 ≤ 600 ∧
      0 ≤ (obliquePoint q).2 ∧ (obliquePoint q).2 ≤ 400 := by sorry
