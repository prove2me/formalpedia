-- Prove2me | Theorems.Thm_Research_obliquePatch_global_normalized_excess
-- name    : Research.obliquePatch_global_normalized_excess
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:08:15.708137+00:00
-- url     : https://prove2.me/theorems/729beb02-eb1e-45e6-8bb0-f1041fa66159
-- title:
--   Research: oblique Patch global normalized excess
-- statement:
--   The finite patch already beats the triangular normalized prediction:
--   `16,786,618 > 126 · 133,225 = 16,786,350`.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L613-L619
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L613-L619

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.obliquePatch_global_normalized_excess :
    126 * Fintype.card (Fin 365 × Fin 365) <
      (radiusSixDirectedPairs obliquePoint).card := by sorry
