-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullSuccessors_rx_q_endpoint_incidence
-- name    : QEC.Coding.BDL26RXIncidenceHullSuccessors.rx_q_endpoint_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:43:27.59159+00:00
-- url     : https://prove2.me/theorems/f4b69957-d10f-44ca-9b83-3c590ac7c179
-- title:
--   BDL26 RXIncidence Hull Successors: rx q endpoint incidence
-- statement:
--   Both endpoints of each actual Q-cylinder edge have its actual successor
--   Z incidence, exhibited by the original X-Q glue face.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullSuccessors.lean#L11-L22
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullSuccessors.lean#L11-L22

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullSuccessors
set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullSuccessors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXIncidenceHullGrowth

theorem QEC.Coding.BDL26RXIncidenceHullSuccessors.rx_q_endpoint_incidence (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    (edge : QDoubleCylinderEdge P q S) (endpoint : BDL26FiniteTannerSquare.Two) :
    (rxReplacementPresentation P S).qz
      (Sum.inr ⟨q, BDL26RXLocalReplacement.edgeEndpoint
        (qDoubleCylinderEdgeStart P q S) (qDoubleCylinderEdgeEnd P q S) edge endpoint⟩)
      (Sum.inl (Sum.inr ⟨q,edge⟩)) = true := by sorry
