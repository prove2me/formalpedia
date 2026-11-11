-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rzDual_qz
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rzDual_qz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:48:39.3349+00:00
-- url     : https://prove2.me/theorems/c2253a57-0142-4768-91c6-0cb8d6c9f83c
-- title:
--   Coordinates: rz Dual qz
-- statement:
--   Actual RZ successor incidence, with both admissibilities derived.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L404-L414
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L404-L414

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TransposedStoppedDecoder QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement hiding Two
open BDL26RZLocalReplacement hiding Two
open BDL26RZMap1CoordinateBridge hiding Two
open BDL26RXDecoderAdapter
open MultiscaleDecoder (BDL26Field)
open scoped Classical BigOperators

theorem QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rzDual_qz (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (q : (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).Q) (z : (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).Z) :
    (rxReplacementPresentation (transposePresentation P) S).qz (rzDualQ P S q) (rzDualZ P S z) = (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).qz q z := by sorry
