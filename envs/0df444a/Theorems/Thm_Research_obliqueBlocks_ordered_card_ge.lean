-- Prove2me | Theorems.Thm_Research_obliqueBlocks_ordered_card_ge
-- name    : Research.obliqueBlocks_ordered_card_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:02:27.734734+00:00
-- url     : https://prove2.me/theorems/87822522-f8d7-563c-acbd-01bef6ed5c2a
-- title:
--   Research: oblique Blocks ordered card ge
-- statement:
--   The direct unordered count in `m` blocks is at least `m·8,393,309`.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L782-L791
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L782-L791

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.obliqueBlocks_ordered_card_ge (m : ℕ) :
    m * 8393309 ≤ (radiusSixOrderedPairs (obliqueBlocks m)).card := by sorry
