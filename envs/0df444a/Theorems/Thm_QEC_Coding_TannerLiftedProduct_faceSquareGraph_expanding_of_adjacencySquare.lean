-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_faceSquareGraph_expanding_of_adjacencySquare
-- name    : QEC.Coding.TannerLiftedProduct.faceSquareGraph_expanding_of_adjacencySquare
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:07:10.159899+00:00
-- url     : https://prove2.me/theorems/ac2b77e9-acbe-47c8-a6b1-c50d0d8df528
-- title:
--   Tanner Lifted Product: face Square Graph expanding of adjacency Square
-- statement:
--   Any small-set expansion bound for the full square adjacency graph applies
--   to the concrete horizontal-then-vertical face graph used by PK22.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L783-L789
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L783-L789

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

theorem QEC.Coding.TannerLiftedProduct.faceSquareGraph_expanding_of_adjacencySquare
    (label : W → G) (radius : Nat) (lambda : ℝ)
    (hSquare : SmallSetExpansion.IsSmallSetEdgeExpanding
      (SmallSetExpansion.square (adjacencyGraph label)) radius lambda) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (faceSquareGraph label) radius lambda := by sorry
