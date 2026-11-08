-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverGraph_isRegular
-- name    : QEC.Coding.TannerLiftedProduct.rightDoubleCoverGraph_isRegular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:01:34.236307+00:00
-- url     : https://prove2.me/theorems/7ce34053-2e29-4ecb-91f0-0c454468f092
-- title:
--   Tanner Lifted Product: right Double Cover Graph is Regular
-- statement:
--   Every double-cover vertex has exactly one outgoing edge for each labelled
--   direction, with parallel labels counted separately.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L267-L274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L267-L274

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

theorem QEC.Coding.TannerLiftedProduct.rightDoubleCoverGraph_isRegular (label : W → G) :
    SmallSetExpansion.IsRegular (rightDoubleCoverGraph label)
      (Fintype.card W) := by sorry
