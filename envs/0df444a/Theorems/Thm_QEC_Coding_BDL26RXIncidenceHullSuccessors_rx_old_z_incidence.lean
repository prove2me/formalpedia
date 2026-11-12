-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullSuccessors_rx_old_z_incidence
-- name    : QEC.Coding.BDL26RXIncidenceHullSuccessors.rx_old_z_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:02:04.764842+00:00
-- url     : https://prove2.me/theorems/55f6dc30-f379-4de2-9c6c-03d420b38285
-- title:
--   BDL26 RXIncidence Hull Successors: rx old z incidence
-- statement:
--   Old Z copy zero joins every incident old Q-cylinder endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullSuccessors.lean#L80-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullSuccessors.lean#L80-L92

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullSuccessors
set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullSuccessors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXIncidenceHullGrowth

theorem QEC.Coding.BDL26RXIncidenceHullSuccessors.rx_old_z_incidence (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    (rxReplacementPresentation P S).qz
      (Sum.inr ⟨q,(0,Sum.inl (Sum.inr (⟨z,hqz⟩ : QStarEdge P q)))⟩)
      (Sum.inr (z,0)) = true := by sorry
