-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_leftDoubleCoverGraph_eq_relabel
-- name    : QEC.Coding.TannerLiftedProduct.leftDoubleCoverGraph_eq_relabel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:05:04.001315+00:00
-- url     : https://prove2.me/theorems/dee1c754-46fa-4d41-b309-5bcaa458cbbd
-- title:
--   Tanner Lifted Product: left Double Cover Graph eq relabel
-- statement:
--   The left and right presentations are graph-isomorphic.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L162-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L162-L183

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_relabel

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
omit [Fintype G] [DecidableEq W]

theorem QEC.Coding.TannerLiftedProduct.leftDoubleCoverGraph_eq_relabel (label : W → G) :
    leftDoubleCoverGraph label =
      SmallSetExpansion.relabel sideInverseEquiv
        (rightDoubleCoverGraph label) := by sorry
