-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightCayleyGraph_reindex
-- name    : QEC.Coding.TannerLiftedProduct.rightCayleyGraph_reindex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:13:27.081485+00:00
-- url     : https://prove2.me/theorems/6a4823b0-80a2-4e7c-a034-2ad58c04ed8d
-- title:
--   Tanner Lifted Product: right Cayley Graph reindex
-- statement:
--   Reindexing the generator directions by an equivalence does not change
--   the labelled Cayley multigraph, including its parallel-edge multiplicities.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L60-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGraphExpansion.lean#L60-L77

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

theorem QEC.Coding.TannerLiftedProduct.rightCayleyGraph_reindex
    {W' : Type v} [Fintype W'] [DecidableEq W']
    (label : W → G) (e : W' ≃ W) :
    rightCayleyGraph (fun a => label (e a)) = rightCayleyGraph label := by sorry
