-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rzDual_xq
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rzDual_xq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:48:31.25597+00:00
-- url     : https://prove2.me/theorems/37007893-caf4-466a-97d8-9d097120e54e
-- title:
--   Coordinates: rz Dual xq
-- statement:
--   Actual RZ successor incidence, with both admissibilities derived.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L391-L401
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L391-L401

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rzDual_xq (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (x : (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).X) (q : (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).Q) :
    (rxReplacementPresentation (transposePresentation P) S).xq (rzDualX P S x) (rzDualQ P S q) = (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).xq x q := by sorry
