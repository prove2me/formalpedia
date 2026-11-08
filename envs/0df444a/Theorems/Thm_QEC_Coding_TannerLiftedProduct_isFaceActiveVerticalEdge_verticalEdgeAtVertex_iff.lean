-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_isFaceActiveVerticalEdge_verticalEdgeAtVertex_iff
-- name    : QEC.Coding.TannerLiftedProduct.isFaceActiveVerticalEdge_verticalEdgeAtVertex_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:03:52.147819+00:00
-- url     : https://prove2.me/theorems/16d0690b-e053-4bb2-bf1e-042b8d2e7469
-- title:
--   Tanner Lifted Product: is Face Active Vertical Edge vertical Edge At Vertex iff
-- statement:
--   The physical-edge face-active predicate agrees with the predicate at any
--   chosen endpoint representation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L675-L687
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L675-L687

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
omit [Fintype F] [Fintype W] [DecidableEq W]
    [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.isFaceActiveVerticalEdge_verticalEdgeAtVertex_iff
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (b : W) :
    IsFaceActiveVerticalEdge label c (verticalEdgeAtVertex label v b) ↔
      IsFaceActiveVerticalEdgeAt label c v b := by sorry
