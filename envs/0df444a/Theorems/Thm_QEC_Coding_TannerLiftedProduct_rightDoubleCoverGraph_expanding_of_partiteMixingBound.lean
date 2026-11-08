-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverGraph_expanding_of_partiteMixingBound
-- name    : QEC.Coding.TannerLiftedProduct.rightDoubleCoverGraph_expanding_of_partiteMixingBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:14:38.043249+00:00
-- url     : https://prove2.me/theorems/46c378b2-8323-4132-832e-fc60764eebe8
-- title:
--   Tanner Lifted Product: right Double Cover Graph expanding of partite Mixing Bound
-- statement:
--   Source-compatible bipartite mixing input for the labelled right double
--   cover.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L492-L500
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L492-L500

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

theorem QEC.Coding.TannerLiftedProduct.rightDoubleCoverGraph_expanding_of_partiteMixingBound
    (label : W → G) (radius : Nat) (spectral density : ℝ)
    (hMixing : HasPartiteExpanderMixingBound
      (rightDoubleCoverGraph label) (Fintype.card W) spectral)
    (hDensity : (Fintype.card W : ℝ) * radius ≤
      density * Fintype.card G) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius (spectral + density) := by sorry
