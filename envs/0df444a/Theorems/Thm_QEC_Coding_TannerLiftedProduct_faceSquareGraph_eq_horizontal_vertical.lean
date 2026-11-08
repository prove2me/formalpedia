-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_faceSquareGraph_eq_horizontal_vertical
-- name    : QEC.Coding.TannerLiftedProduct.faceSquareGraph_eq_horizontal_vertical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:07:12.525768+00:00
-- url     : https://prove2.me/theorems/ab036d6f-f61f-456d-8470-d690d3799c64
-- title:
--   Tanner Lifted Product: face Square Graph eq horizontal vertical
-- statement:
--   Horizontal-then-vertical local face paths are the corresponding product
--   of the two one-step adjacency matrices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L754-L761
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L754-L761

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

theorem QEC.Coding.TannerLiftedProduct.faceSquareGraph_eq_horizontal_vertical (label : W → G)
    (v u : VertexIndex G) :
    faceSquareGraph label v u =
      ∑ x, horizontalGraph label v x * verticalGraph label x u := by sorry
