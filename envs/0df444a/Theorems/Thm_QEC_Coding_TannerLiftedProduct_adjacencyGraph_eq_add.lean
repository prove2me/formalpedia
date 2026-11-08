-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_adjacencyGraph_eq_add
-- name    : QEC.Coding.TannerLiftedProduct.adjacencyGraph_eq_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:01:55.103614+00:00
-- url     : https://prove2.me/theorems/df272f21-108a-43b7-b448-213a45bbd184
-- title:
--   Tanner Lifted Product: adjacency Graph eq add
-- statement:
--   The concrete adjacency graph is the union of its horizontal and vertical
--   parts.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L596-L599
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L596-L599

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_add
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
omit [Fintype G] [DecidableEq W]

theorem QEC.Coding.TannerLiftedProduct.adjacencyGraph_eq_add (label : W → G) :
    adjacencyGraph label =
      SmallSetExpansion.add (horizontalGraph label) (verticalGraph label) := by sorry
