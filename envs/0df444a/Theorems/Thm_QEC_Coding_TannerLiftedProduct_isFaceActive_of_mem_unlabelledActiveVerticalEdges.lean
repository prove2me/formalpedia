-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_isFaceActive_of_mem_unlabelledActiveVerticalEdges
-- name    : QEC.Coding.TannerLiftedProduct.isFaceActive_of_mem_unlabelledActiveVerticalEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:03:12.048207+00:00
-- url     : https://prove2.me/theorems/507ccb32-c1b2-426a-bb9f-1a19f41d3f42
-- title:
--   Tanner Lifted Product: is Face Active of mem unlabelled Active Vertical Edges
-- statement:
--   If `L` contains every active vertex, an active edge with no labelled
--   endpoint is face-active.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L575-L600
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L575-L600

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
omit [Fintype F] [DecidableEq W] [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.isFaceActive_of_mem_unlabelledActiveVerticalEdges
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (L : Finset (VertexIndex G))
    (hActive : vertexBlockSupport c ⊆ L)
    (e : VerticalEdgeIndex W G)
    (he : e ∈ unlabelledActiveVerticalEdges label c L) :
    IsFaceActiveVerticalEdge label c e := by sorry
