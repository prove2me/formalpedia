-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rxDual_coboundary1
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rxDual_coboundary1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:47:44.029126+00:00
-- url     : https://prove2.me/theorems/cbdb5e98-b0af-44fc-b8cb-6f6f2e1b7314
-- title:
--   Coordinates: rx Dual coboundary1
-- statement:
--   The literal successor coordinate equivalence intertwines degree 1.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L376-L388
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L376-L388

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rxDual_coboundary1 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Word BDL26Field (transposePresentation (rxReplacementPresentation P S)).Q) :
    tannerCoboundary1 (rzReplacementPresentation (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S) (wordEquiv (rxDualQ P S) w) =
      wordEquiv (rxDualZ P S) (tannerCoboundary1 (transposePresentation (rxReplacementPresentation P S)) w) := by sorry
