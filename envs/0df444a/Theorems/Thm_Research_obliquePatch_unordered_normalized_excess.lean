-- Prove2me | Theorems.Thm_Research_obliquePatch_unordered_normalized_excess
-- name    : Research.obliquePatch_unordered_normalized_excess
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:08:14.226709+00:00
-- url     : https://prove2.me/theorems/0891b836-ddc2-413a-8791-958331059111
-- title:
--   Research: oblique Patch unordered normalized excess
-- statement:
--   Direct unordered form of the same strict excess:
--   `8,393,309 > 63 · 133,225 = 8,393,175`.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L623-L629
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L623-L629

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.obliquePatch_unordered_normalized_excess :
    63 * Fintype.card (Fin 365 × Fin 365) <
      (radiusSixOrderedPairs obliquePoint).card := by sorry
