-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rxDual_coboundary0
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rxDual_coboundary0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:47:14.450201+00:00
-- url     : https://prove2.me/theorems/5802d92c-e87f-4fd9-818e-06ab37c9e6ee
-- title:
--   Coordinates: rx Dual coboundary0
-- statement:
--   The literal successor coordinate equivalence intertwines degree 0.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L361-L373
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L361-L373

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rxDual_coboundary0 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Word BDL26Field (transposePresentation (rxReplacementPresentation P S)).X) :
    tannerCoboundary0 (rzReplacementPresentation (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S) (wordEquiv (rxDualX P S) w) =
      wordEquiv (rxDualQ P S) (tannerCoboundary0 (transposePresentation (rxReplacementPresentation P S)) w) := by sorry
