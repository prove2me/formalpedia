-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_faceSquareGraph_expanding_of_doubleCover
-- name    : QEC.Coding.TannerLiftedProduct.faceSquareGraph_expanding_of_doubleCover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:08:03.70245+00:00
-- url     : https://prove2.me/theorems/de063e00-eccc-4052-bf30-320463712d2c
-- title:
--   Tanner Lifted Product: face Square Graph expanding of double Cover
-- statement:
--   The concrete face graph receives the square-graph expansion bound needed
--   by the global labelled-set argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L794-L805
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L794-L805

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

theorem QEC.Coding.TannerLiftedProduct.faceSquareGraph_expanding_of_doubleCover
    (label : W → G) (radius : Nat) (lambda : ℝ)
    (hLambda : 0 ≤ lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (faceSquareGraph label) (radius / (2 * Fintype.card W))
      (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) := by sorry
