-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_adjacencyGraph_isRegular
-- name    : QEC.Coding.TannerLiftedProduct.adjacencyGraph_isRegular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:05:43.583168+00:00
-- url     : https://prove2.me/theorems/005e4a0e-3348-4eae-82ba-fbf7a4ecb4e1
-- title:
--   Tanner Lifted Product: adjacency Graph is Regular
-- statement:
--   Every product vertex has `2 * |W|` outgoing adjacency directions,
--   counted with multiplicity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L619-L646
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L619-L646

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

theorem QEC.Coding.TannerLiftedProduct.adjacencyGraph_isRegular (label : W → G) :
    SmallSetExpansion.IsRegular (adjacencyGraph label)
      (2 * Fintype.card W) := by sorry
