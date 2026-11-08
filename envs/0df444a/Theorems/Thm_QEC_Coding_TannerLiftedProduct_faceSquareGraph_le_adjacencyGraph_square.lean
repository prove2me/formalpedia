-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_faceSquareGraph_le_adjacencyGraph_square
-- name    : QEC.Coding.TannerLiftedProduct.faceSquareGraph_le_adjacencyGraph_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:07:21.398904+00:00
-- url     : https://prove2.me/theorems/d8592557-9452-465b-8d4e-7d31d089caed
-- title:
--   Tanner Lifted Product: face Square Graph le adjacency Graph square
-- statement:
--   The local face-path graph is a pointwise subgraph of the full square of
--   the horizontal-plus-vertical adjacency graph.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L766-L778
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L766-L778

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

theorem QEC.Coding.TannerLiftedProduct.faceSquareGraph_le_adjacencyGraph_square (label : W → G)
    (v u : VertexIndex G) :
    faceSquareGraph label v u ≤
      SmallSetExpansion.square (adjacencyGraph label) v u := by sorry
