-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_verticalFaceGraph_expanding_of_doubleCover
-- name    : QEC.Coding.TannerLiftedProduct.verticalFaceGraph_expanding_of_doubleCover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:07:13.598274+00:00
-- url     : https://prove2.me/theorems/77eb8c35-9ce4-42ac-a7b9-0b59d8cc6ed9
-- title:
--   Tanner Lifted Product: vertical Face Graph expanding of double Cover
-- statement:
--   The physical vertical-edge graph inherits the base mixing constant with
--   no loss in the number of local vertical directions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L740-L749
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L740-L749

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
omit [Fintype G]

theorem QEC.Coding.TannerLiftedProduct.verticalFaceGraph_expanding_of_doubleCover
    (label : W → G) (radius : Nat) (lambda : ℝ)
    (hLambda : 0 ≤ lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (verticalFaceGraph label) radius lambda := by sorry
