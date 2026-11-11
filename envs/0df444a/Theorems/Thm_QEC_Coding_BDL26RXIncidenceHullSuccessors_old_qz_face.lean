-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullSuccessors_old_qz_face
-- name    : QEC.Coding.BDL26RXIncidenceHullSuccessors.old_qz_face
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:59:02.065809+00:00
-- url     : https://prove2.me/theorems/490f5c49-44b6-4d33-a975-86287dd1a0c9
-- title:
--   BDL26 RXIncidence Hull Successors: old qz face
-- statement:
--   Every old Q--Z incidence has a materialized old-face corner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullSuccessors.lean#L71-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullSuccessors.lean#L71-L77

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullSuccessors
set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullSuccessors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXIncidenceHullGrowth

theorem QEC.Coding.BDL26RXIncidenceHullSuccessors.old_qz_face (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    ∃ f : P.Face, ∃ corner : BDL26FiniteTannerSquare.Two, P.faceQ f corner = q ∧ P.faceZ f = z := by sorry
