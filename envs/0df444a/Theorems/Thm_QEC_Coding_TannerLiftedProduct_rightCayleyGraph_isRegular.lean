-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightCayleyGraph_isRegular
-- name    : QEC.Coding.TannerLiftedProduct.rightCayleyGraph_isRegular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:04:31.901488+00:00
-- url     : https://prove2.me/theorems/944a2a63-edfd-4af1-b75a-bc6d40d0e79f
-- title:
--   Tanner Lifted Product: right Cayley Graph is Regular
-- statement:
--   The labelled Cayley multigraph has one outgoing edge for every labelled
--   generator direction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L82-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L82-L88

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

theorem QEC.Coding.TannerLiftedProduct.rightCayleyGraph_isRegular (label : W → G) :
    SmallSetExpansion.IsRegular (rightCayleyGraph label)
      (Fintype.card W) := by sorry
