-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverGraph_isSymmetric
-- name    : QEC.Coding.TannerLiftedProduct.rightDoubleCoverGraph_isSymmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:02:43.327947+00:00
-- url     : https://prove2.me/theorems/30e8c9ab-83d1-45be-94e9-6786366bdeb6
-- title:
--   Tanner Lifted Product: right Double Cover Graph is Symmetric
-- statement:
--   The labelled right double cover is symmetric because every labelled
--   direction is an involution after switching sides.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L259-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L259-L262

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

theorem QEC.Coding.TannerLiftedProduct.rightDoubleCoverGraph_isSymmetric (label : W → G) :
    SmallSetExpansion.IsSymmetric (rightDoubleCoverGraph label) := by sorry
