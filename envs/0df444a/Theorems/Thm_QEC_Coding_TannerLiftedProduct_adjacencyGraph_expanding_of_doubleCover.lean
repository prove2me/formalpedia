-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_adjacencyGraph_expanding_of_doubleCover
-- name    : QEC.Coding.TannerLiftedProduct.adjacencyGraph_expanding_of_doubleCover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:01:47.941247+00:00
-- url     : https://prove2.me/theorems/0a88b1f6-6915-4523-9ed4-be4a31628a9d
-- title:
--   Tanner Lifted Product: adjacency Graph expanding of double Cover
-- statement:
--   PK22 `lemma:expG'`: the product adjacency graph inherits twice the base
--   mixing constant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L691-L710
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L691-L710

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
omit [Fintype G] [DecidableEq W]

theorem QEC.Coding.TannerLiftedProduct.adjacencyGraph_expanding_of_doubleCover
    (label : W → G) (radius : Nat) (lambda : ℝ)
    (hLambda : 0 ≤ lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (adjacencyGraph label) radius (2 * lambda) := by sorry
