-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_gauge_strip_parity
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocal_gauge_strip_parity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:33:24.637229+00:00
-- url     : https://prove2.me/theorems/40aa2b55-3ecf-4150-90ef-95fba101fa79
-- title:
--   BDL26 RXLocal Replacement: x Local gauge strip parity
-- statement:
--   The radial gauge changes neither boundary-strip parity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeightCertificates.lean#L63-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeightCertificates.lean#L63-L75

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightCertificates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity BDL26XLocalConnectingWeight
open BDL26XLocalRadialParity
open scoped BigOperators

theorem QEC.Coding.BDL26RXLocalReplacement.xLocal_gauge_strip_parity
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (selected : Two) (alpha : Neighbor P x → Field)
    (face : XStarFace P x) (side : Two) :
    xLocalRegionParity P x S
        (wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
          (radialGauge P A x S selected alpha)) face (Sum.inr side) = 0 := by sorry
