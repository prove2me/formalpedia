-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rxDualFace_Q
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rxDualFace_Q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:22:18.747145+00:00
-- url     : https://prove2.me/theorems/1ab549f0-ac79-4416-ae34-1ba6c99def5e
-- title:
--   Coordinates: rx Dual Face Q
-- statement:
--   Both ordered Q corners commute; neither corner order nor pieces are changed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L262-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L262-L278

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rxDualFace_Q (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible (transposePresentation P)) (S : OddScale)
    (f : RXFace P S) (b : Two) :
    rzFaceQ (transposePresentation P) A S (rxDualFace P S f) b =
      rxDualQ P S (rxFaceQ P S f b) := by sorry
