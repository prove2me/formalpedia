-- Prove2me | Theorems.Thm_Research_obliquePatch_ordered_card_ge
-- name    : Research.obliquePatch_ordered_card_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:58:27.311693+00:00
-- url     : https://prove2.me/theorems/ac85b947-317a-4e7c-90ba-cd10fc68baf8
-- title:
--   Research: oblique Patch ordered card ge
-- statement:
--   At least 8,393,309 direct unordered pairs occur in the finite patch.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L604-L609
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L604-L609

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.obliquePatch_ordered_card_ge :
    8393309 ≤ (radiusSixOrderedPairs obliquePoint).card := by sorry
