-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_sum_verticalFaceGraph_eq_card_filter
-- name    : QEC.Coding.TannerLiftedProduct.sum_verticalFaceGraph_eq_card_filter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:59:34.874969+00:00
-- url     : https://prove2.me/theorems/15fd5d86-4e0a-4a24-b2a5-d50860b47050
-- title:
--   Tanner Lifted Product: sum vertical Face Graph eq card filter
-- statement:
--   Outgoing face multiplicity into a physical-edge set counts exactly the
--   local horizontal directions whose opposite vertical edge lies in that set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L189-L198
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L189-L198

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.sum_verticalFaceGraph_eq_card_filter
    (label : W → G) (A : Finset (VerticalEdgeIndex W G))
    (e : VerticalEdgeIndex W G) :
    ∑ e' ∈ A, verticalFaceGraph label e e' =
      (Finset.univ.filter fun a : W =>
        verticalFaceNeighbor label e a ∈ A).card := by sorry
