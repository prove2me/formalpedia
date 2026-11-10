-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_gauge_makes_pieces_even
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocal_gauge_makes_pieces_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:43:54.909044+00:00
-- url     : https://prove2.me/theorems/55f6b1dd-d323-401a-8b0b-5e9575caff96
-- title:
--   BDL26 RXLocal Replacement: x Local gauge makes pieces even
-- statement:
--   The interface parities of the given preimage make every updated piece even.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeightCertificates.lean#L85-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeightCertificates.lean#L85-L111

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightCertificates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity BDL26XLocalConnectingWeight
open BDL26XLocalRadialParity
open scoped BigOperators

theorem QEC.Coding.BDL26RXLocalReplacement.xLocal_gauge_makes_pieces_even
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (e : Word Field (DoubleCylinderEdge P x S))
    (selected : Two) (face : XStarFace P x) :
    let D := wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
    let tau := D e + D (radialGauge P A x S selected (interfaceParity P A x S e))
    xLocalRegionParity P x S tau face (Sum.inl 0) +
      xLocalRegionParity P x S tau face (Sum.inl 1) +
      xLocalRegionParity P x S tau face (Sum.inr 0) +
      xLocalRegionParity P x S tau face (Sum.inr 1) = 0 := by sorry
