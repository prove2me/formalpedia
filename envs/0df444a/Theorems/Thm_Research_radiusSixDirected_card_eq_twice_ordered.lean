-- Prove2me | Theorems.Thm_Research_radiusSixDirected_card_eq_twice_ordered
-- name    : Research.radiusSixDirected_card_eq_twice_ordered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:51:56.965126+00:00
-- url     : https://prove2.me/theorems/71eecb1c-da0c-5c0b-95a0-eba3c8b89feb
-- title:
--   Research: radius Six Directed card eq twice ordered
-- statement:
--   Every unordered radius-six pair contributes exactly its two orientations to
--   the directed count.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L554-L601
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L554-L601

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.radiusSixDirected_card_eq_twice_ordered {α : Type*}
    [Fintype α] [DecidableEq α] [LinearOrder α] (p : α → ℝ × ℝ) :
    (radiusSixDirectedPairs p).card =
      2 * (radiusSixOrderedPairs p).card := by sorry
