-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_leftDoubleCoverGraph_expanding
-- name    : QEC.Coding.TannerLiftedProduct.leftDoubleCoverGraph_expanding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:06:10.184585+00:00
-- url     : https://prove2.me/theorems/2d26d0b8-a6b0-4ddd-99b6-9f2dcee20447
-- title:
--   Tanner Lifted Product: left Double Cover Graph expanding
-- statement:
--   The two multiplication presentations have identical small-set expansion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L679-L686
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L679-L686

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

theorem QEC.Coding.TannerLiftedProduct.leftDoubleCoverGraph_expanding
    (label : W → G) (radius : Nat) (lambda : ℝ)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (leftDoubleCoverGraph label) radius lambda := by sorry
