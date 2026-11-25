-- Prove2me | Theorems.Thm_Research_radiusSixOrdinaryDirectedPairs_eq
-- name    : Research.radiusSixOrdinaryDirectedPairs_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:48:07.872624+00:00
-- url     : https://prove2.me/theorems/110cf431-9f30-541a-890e-0f7c33b8bde1
-- title:
--   Research: radius Six Ordinary Directed Pairs eq
-- statement:
--   Ordinary- and squared-distance directed definitions agree exactly.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L422-L438
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L422-L438

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.radiusSixOrdinaryDirectedPairs_eq {α : Type*} [Fintype α]
    [DecidableEq α] (p : α → ℝ × ℝ) :
    radiusSixOrdinaryDirectedPairs p = radiusSixDirectedPairs p := by sorry
