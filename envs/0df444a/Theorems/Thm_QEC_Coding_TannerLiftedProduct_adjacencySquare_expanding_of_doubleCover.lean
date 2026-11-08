-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_adjacencySquare_expanding_of_doubleCover
-- name    : QEC.Coding.TannerLiftedProduct.adjacencySquare_expanding_of_doubleCover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:07:25.891754+00:00
-- url     : https://prove2.me/theorems/f9d716e1-2415-46bd-bc32-e9dee828a0f1
-- title:
--   Tanner Lifted Product: adjacency Square expanding of double Cover
-- statement:
--   PK22 `lemma:expG''`, in a dyadic form: the square of product adjacency
--   has radius divided by `2 * |W|` and mixing constant
--   `8 * lambda² * (log₂(2|W|) + 1)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L716-L735
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L716-L735

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
omit [DecidableEq W]

theorem QEC.Coding.TannerLiftedProduct.adjacencySquare_expanding_of_doubleCover
    (label : W → G) (radius : Nat) (lambda : ℝ)
    (hLambda : 0 ≤ lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (SmallSetExpansion.square (adjacencyGraph label))
      (radius / (2 * Fintype.card W))
      (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) := by sorry
