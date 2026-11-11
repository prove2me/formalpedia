-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rzDual_coboundary1
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rzDual_coboundary1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:48:25.148924+00:00
-- url     : https://prove2.me/theorems/6eff3edb-17fd-475d-90c8-a95d0e193637
-- title:
--   Coordinates: rz Dual coboundary1
-- statement:
--   The literal successor coordinate equivalence intertwines degree 1.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L430-L440
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L430-L440

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rzDual_coboundary1 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Word BDL26Field (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).Q) :
    tannerCoboundary1 (rxReplacementPresentation (transposePresentation P) S) (wordEquiv (rzDualQ P S) w) =
      wordEquiv (rzDualZ P S) (tannerCoboundary1 (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)) w) := by sorry
