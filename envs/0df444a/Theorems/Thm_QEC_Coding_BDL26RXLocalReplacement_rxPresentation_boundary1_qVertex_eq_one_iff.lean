-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_boundary1_qVertex_eq_one_iff
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxPresentation_boundary1_qVertex_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:41:31.20214+00:00
-- url     : https://prove2.me/theorems/39d24a08-f465-48f8-8d04-13d53884e54f
-- title:
--   BDL26 RXLocal Replacement: rx Presentation boundary1 q Vertex eq one iff
-- statement:
--   The shifted Q-local branch has exactly its materialized face incidences.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPresentationCochain.lean#L260-L298
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPresentationCochain.lean#L260-L298

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped BigOperators

theorem QEC.Coding.BDL26RXLocalReplacement.rxPresentation_boundary1_qVertex_eq_one_iff
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (v : RX0 P S)
    (qv : Σ q : P.Q, QDoubleCylinderVertex P q S) :
    rxBoundary1Matrix P S v (Sum.inr qv) = 1 ↔
      rxXQIncidence P S v (Sum.inr qv) = true := by sorry
