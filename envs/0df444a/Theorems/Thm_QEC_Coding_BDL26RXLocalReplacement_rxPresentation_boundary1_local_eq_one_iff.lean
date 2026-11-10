-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_boundary1_local_eq_one_iff
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxPresentation_boundary1_local_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:41:03.146212+00:00
-- url     : https://prove2.me/theorems/ac6d85aa-a105-4bb2-9599-4273eebfc0a4
-- title:
--   BDL26 RXLocal Replacement: rx Presentation boundary1 local eq one iff
-- statement:
--   The X-local branch has exactly its two explicit endpoint incidences.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPresentationCochain.lean#L166-L196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPresentationCochain.lean#L166-L196

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped BigOperators

theorem QEC.Coding.BDL26RXLocalReplacement.rxPresentation_boundary1_local_eq_one_iff
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (v : RX0 P S)
    (edge : Σ x : P.X, DoubleCylinderEdge P x S) :
    rxBoundary1Matrix P S v (Sum.inl edge) = 1 ↔
      rxXQIncidence P S v (Sum.inl edge) = true := by sorry
