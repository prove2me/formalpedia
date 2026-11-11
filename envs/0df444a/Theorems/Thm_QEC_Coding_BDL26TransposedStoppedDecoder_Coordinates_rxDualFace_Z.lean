-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rxDualFace_Z
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rxDualFace_Z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:45:38.921902+00:00
-- url     : https://prove2.me/theorems/c4705e83-ebab-4cab-bc80-9bb5df240954
-- title:
--   Coordinates: rx Dual Face Z
-- statement:
--   The other check endpoint retains the actual raw glue endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L238-L259
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L238-L259

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rxDualFace_Z (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible (transposePresentation P)) (S : OddScale)
    (f : RXFace P S) :
    rzFaceZ (transposePresentation P) A S (rxDualFace P S f) =
      rxDualZ P S (rxFaceX P S f) := by sorry
