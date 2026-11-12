-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullSuccessors_rx_q_cylinder_connected
-- name    : QEC.Coding.BDL26RXIncidenceHullSuccessors.rx_q_cylinder_connected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:42:55.056146+00:00
-- url     : https://prove2.me/theorems/62001c33-717c-4bd7-b3a4-47b729ea87da
-- title:
--   BDL26 RXIncidence Hull Successors: rx q cylinder connected
-- statement:
--   Every vertex in the actual Q-local cylinder lies in its root component,
--   including both copies and all interior and endpoint coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullSuccessors.lean#L63-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullSuccessors.lean#L63-L68

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullSuccessors
set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullSuccessors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXIncidenceHullGrowth

theorem QEC.Coding.BDL26RXIncidenceHullSuccessors.rx_q_cylinder_connected (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    (u v : QDoubleCylinderVertex P q S) :
    SharedZPath (rxReplacementPresentation P S) (Sum.inr ⟨q,u⟩) (Sum.inr ⟨q,v⟩) := by sorry
