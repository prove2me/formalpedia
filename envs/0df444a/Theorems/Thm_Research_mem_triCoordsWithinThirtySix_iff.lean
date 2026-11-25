-- Prove2me | Theorems.Thm_Research_mem_triCoordsWithinThirtySix_iff
-- name    : Research.mem_triCoordsWithinThirtySix_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:57:19.983638+00:00
-- url     : https://prove2.me/theorems/1e2d2a09-5d30-4ee2-9ec5-ff5b4cc9ed5a
-- title:
--   Research: mem tri Coords Within Thirty Six iff
-- statement:
--   Completeness characterization for the radius-six triangular census.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L186-L199
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L186-L199

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.mem_triCoordsWithinThirtySix_iff (d : ℤ × ℤ) :
    d ∈ triCoordsWithinThirtySix ↔
      d ≠ (0, 0) ∧ triNormSq d ≤ 36 := by sorry
