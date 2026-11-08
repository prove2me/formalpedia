-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_sum_adjacencyGraph_eq_card_directionsInto
-- name    : QEC.Coding.TannerLiftedProduct.sum_adjacencyGraph_eq_card_directionsInto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:40:08.2552+00:00
-- url     : https://prove2.me/theorems/fd20abd3-c1d0-42b4-b387-780c94c04d38
-- title:
--   Tanner Lifted Product: sum adjacency Graph eq card directions Into
-- statement:
--   Outgoing adjacency multiplicity into a vertex set is exactly the number
--   of horizontal and vertical local directions entering it.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L69-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L69-L80

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
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
    [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.sum_adjacencyGraph_eq_card_directionsInto
    (label : W → G) (L : Finset (VertexIndex G)) (v : VertexIndex G) :
    ∑ u ∈ L, adjacencyGraph label v u =
      (horizontalDirectionsInto label L v).card +
        (verticalDirectionsInto label L v).card := by sorry
