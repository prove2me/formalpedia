-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_xEdge_endpoint_incidence
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxPresentation_xEdge_endpoint_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:21:58.286547+00:00
-- url     : https://prove2.me/theorems/29ba24cf-71a0-4df3-b8ab-b17892f09146
-- title:
--   BDL26 RXLocal Replacement: rx Presentation x Edge endpoint incidence
-- statement:
--   Every endpoint of an X-local edge occurs in a materialized RX face.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPresentationCochain.lean#L132-L163
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPresentationCochain.lean#L132-L163

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped BigOperators

theorem QEC.Coding.BDL26RXLocalReplacement.rxPresentation_xEdge_endpoint_incidence
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (S : OddScale) (x : P.X) (edge : DoubleCylinderEdge P x S)
    (endpoint : Two) :
    rxXQIncidence P S
      ⟨x, edgeEndpoint (tannerDoubleCylinderEdgeStart P x S)
        (tannerDoubleCylinderEdgeEnd P x S) edge endpoint⟩
      (Sum.inl ⟨x, edge⟩) = true := by sorry
