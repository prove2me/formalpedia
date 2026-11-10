-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_gauge_layer_parity
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocal_gauge_layer_parity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:33:15.481473+00:00
-- url     : https://prove2.me/theorems/50213fe3-7f94-4b7f-8f16-e185645c7277
-- title:
--   BDL26 RXLocal Replacement: x Local gauge layer parity
-- statement:
--   The radial gauge changes exactly the selected layer's piece parity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeightCertificates.lean#L35-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeightCertificates.lean#L35-L60

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightCertificates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity BDL26XLocalConnectingWeight
open BDL26XLocalRadialParity
open scoped BigOperators

theorem QEC.Coding.BDL26RXLocalReplacement.xLocal_gauge_layer_parity
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (selected : Two) (alpha : Neighbor P x → Field)
    (face : XStarFace P x) (copy : Two) :
    xLocalRegionParity P x S
        (wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
          (radialGauge P A x S selected alpha)) face (Sum.inl copy) =
      if copy = selected then alpha (faceNeighbor P x face 0) +
        alpha (faceNeighbor P x face 1) else 0 := by sorry
