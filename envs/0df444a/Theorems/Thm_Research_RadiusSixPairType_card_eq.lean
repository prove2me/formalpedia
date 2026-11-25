-- Prove2me | Theorems.Thm_Research_RadiusSixPairType_card_eq
-- name    : Research.RadiusSixPairType_card_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:48:14.316659+00:00
-- url     : https://prove2.me/theorems/b7f0a0c9-ed4f-4f56-94a6-9dad41b336e5
-- title:
--   Research: Radius Six Pair Type card eq
-- statement:
--   The predicate-subtype cardinality agrees with the direct finset count.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L454-L465
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L454-L465

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.RadiusSixPairType_card_eq {α : Type*} [Fintype α]
    [DecidableEq α] (p : α → ℝ × ℝ) :
    Fintype.card (RadiusSixPairType p) = (radiusSixDirectedPairs p).card := by sorry
