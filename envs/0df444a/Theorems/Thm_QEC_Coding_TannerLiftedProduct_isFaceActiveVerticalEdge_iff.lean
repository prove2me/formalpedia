-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_isFaceActiveVerticalEdge_iff
-- name    : QEC.Coding.TannerLiftedProduct.isFaceActiveVerticalEdge_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:59:02.883225+00:00
-- url     : https://prove2.me/theorems/9210b4c6-0b56-42b5-89a4-96a6e69b8946
-- title:
--   Tanner Lifted Product: is Face Active Vertical Edge iff
-- statement:
--   A face-active physical edge is the same source predicate at its
--   canonical endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L606-L615
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L606-L615

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
omit [Fintype F] [DecidableEq G] [Fintype W] [DecidableEq W]
    [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.isFaceActiveVerticalEdge_iff (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (e : VerticalEdgeIndex W G) :
    IsFaceActiveVerticalEdge label c e ↔
      CarriesActiveFaceVerticalEdge label c e ∧
      verticalEdgeEndpoint label e 0 ∉ vertexBlockSupport c ∧
      verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1 ∉
        vertexBlockSupport c := by sorry
