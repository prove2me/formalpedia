-- Prove2me | Theorems.Thm_Research_obliqueBlocks_global_normalized_excess
-- name    : Research.obliqueBlocks_global_normalized_excess
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:52:47.710375+00:00
-- url     : https://prove2.me/theorems/91a3f872-e056-4392-b14f-f71e03bcaf3c
-- title:
--   Research: oblique Blocks global normalized excess
-- statement:
--   Every nonempty collection of blocks violates the directed normalized
--   triangular bound at shell radius six.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L768-L779
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L768-L779

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.obliqueBlocks_global_normalized_excess (m : ℕ) (hm : 0 < m) :
    126 * Fintype.card (Fin m × (Fin 365 × Fin 365)) <
      (radiusSixDirectedPairs (obliqueBlocks m)).card := by sorry
