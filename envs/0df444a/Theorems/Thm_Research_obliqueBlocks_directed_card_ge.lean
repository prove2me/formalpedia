-- Prove2me | Theorems.Thm_Research_obliqueBlocks_directed_card_ge
-- name    : Research.obliqueBlocks_directed_card_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:52:16.212645+00:00
-- url     : https://prove2.me/theorems/b722aeaf-a531-5879-98e4-77e445d31ccf
-- title:
--   Research: oblique Blocks directed card ge
-- statement:
--   `m` blocks retain at least `m·16,786,618` directed radius-six pairs.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L756-L764
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L756-L764

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.obliqueBlocks_directed_card_ge (m : ℕ) :
    m * 16786618 ≤ (radiusSixDirectedPairs (obliqueBlocks m)).card := by sorry
