-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullSuccessors_rx_q_end_incidence
-- name    : QEC.Coding.BDL26RXIncidenceHullSuccessors.rx_q_end_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:00:02.081832+00:00
-- url     : https://prove2.me/theorems/a233f0d9-1366-4a43-ac14-107c2f99e864
-- title:
--   BDL26 RXIncidence Hull Successors: rx q end incidence
-- statement:
--   The BDL26 RXIncidence Hull Successors construction uses the rx q end incidence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullSuccessors.lean#L33-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullSuccessors.lean#L33-L40

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullSuccessors
set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullSuccessors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXIncidenceHullGrowth

theorem QEC.Coding.BDL26RXIncidenceHullSuccessors.rx_q_end_incidence (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    (edge : QDoubleCylinderEdge P q S) :
    (rxReplacementPresentation P S).qz
      (Sum.inr ⟨q,qDoubleCylinderEdgeEnd P q S edge⟩)
      (Sum.inl (Sum.inr ⟨q,edge⟩)) = true := by sorry
