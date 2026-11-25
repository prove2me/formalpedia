-- Prove2me | Theorems.Thm_Research_radiusSixOrdinaryOrderedPairs_eq
-- name    : Research.radiusSixOrdinaryOrderedPairs_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:48:11.39666+00:00
-- url     : https://prove2.me/theorems/64208d02-7d70-5a96-8877-ed35adaf7167
-- title:
--   Research: radius Six Ordinary Ordered Pairs eq
-- statement:
--   Ordinary- and squared-distance direct unordered definitions agree exactly.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L480-L496
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L480-L496

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.radiusSixOrdinaryOrderedPairs_eq {α : Type*} [Fintype α]
    [LinearOrder α] (p : α → ℝ × ℝ) :
    radiusSixOrdinaryOrderedPairs p = radiusSixOrderedPairs p := by sorry
