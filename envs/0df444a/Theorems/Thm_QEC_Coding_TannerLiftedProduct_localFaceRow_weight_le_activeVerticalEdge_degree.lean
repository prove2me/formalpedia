-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_localFaceRow_weight_le_activeVerticalEdge_degree
-- name    : QEC.Coding.TannerLiftedProduct.localFaceRow_weight_le_activeVerticalEdge_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:03:04.21299+00:00
-- url     : https://prove2.me/theorems/76c3c25d-11c0-420b-8537-ac156b27c8cf
-- title:
--   Tanner Lifted Product: local Face Row weight le active Vertical Edge degree
-- statement:
--   Every nonzero face direction at `e` leads to an active opposite vertical
--   edge, so face-row weight is bounded by degree into the active-edge set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L528-L550
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L528-L550

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
omit [Fintype F] [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.localFaceRow_weight_le_activeVerticalEdge_degree
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (e : VerticalEdgeIndex W G) :
    HammingWeight
        (ProductExpansion.row
          (localFaceMatrix label c (verticalEdgeEndpoint label e 0)) e.2.1) ≤
      ∑ e' ∈ activeVerticalEdges label c, verticalFaceGraph label e e' := by sorry
