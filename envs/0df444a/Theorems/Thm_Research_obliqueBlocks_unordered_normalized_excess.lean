-- Prove2me | Theorems.Thm_Research_obliqueBlocks_unordered_normalized_excess
-- name    : Research.obliqueBlocks_unordered_normalized_excess
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:52:36.358042+00:00
-- url     : https://prove2.me/theorems/eb57596c-35e3-5139-8610-5d422d2038c3
-- title:
--   Research: oblique Blocks unordered normalized excess
-- statement:
--   Every nonempty collection of blocks also violates the direct unordered
--   bound `E₆ ≤ 63n`.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L795-L806
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L795-L806

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.obliqueBlocks_unordered_normalized_excess (m : ℕ) (hm : 0 < m) :
    63 * Fintype.card (Fin m × (Fin 365 × Fin 365)) <
      (radiusSixOrderedPairs (obliqueBlocks m)).card := by sorry
