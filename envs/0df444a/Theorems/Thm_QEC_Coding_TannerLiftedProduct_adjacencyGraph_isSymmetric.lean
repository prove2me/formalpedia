-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_adjacencyGraph_isSymmetric
-- name    : QEC.Coding.TannerLiftedProduct.adjacencyGraph_isSymmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:05:34.77305+00:00
-- url     : https://prove2.me/theorems/83db6bf0-d42c-4889-b6f2-51dde34d42ae
-- title:
--   Tanner Lifted Product: adjacency Graph is Symmetric
-- statement:
--   The horizontal-plus-vertical Tanner adjacency multigraph is symmetric.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L603-L614
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L603-L614

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

theorem QEC.Coding.TannerLiftedProduct.adjacencyGraph_isSymmetric (label : W → G) :
    SmallSetExpansion.IsSymmetric (adjacencyGraph label) := by sorry
