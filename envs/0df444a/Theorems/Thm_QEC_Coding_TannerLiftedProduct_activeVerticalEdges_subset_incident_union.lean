-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_activeVerticalEdges_subset_incident_union
-- name    : QEC.Coding.TannerLiftedProduct.activeVerticalEdges_subset_incident_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:02:22.429193+00:00
-- url     : https://prove2.me/theorems/2fb050b1-7888-48c2-a3f5-5479f01cec43
-- title:
--   Tanner Lifted Product: active Vertical Edges subset incident union
-- statement:
--   Every active physical vertical edge is covered by an active endpoint
--   vertex or one of the two vertical sides of an active face.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L255-L285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L255-L285

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

theorem QEC.Coding.TannerLiftedProduct.activeVerticalEdges_subset_incident_union
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    activeVerticalEdges label c ⊆
      activeVertexIncidentVerticalEdges label c ∪
        activeFaceIncidentVerticalEdges label c := by sorry
