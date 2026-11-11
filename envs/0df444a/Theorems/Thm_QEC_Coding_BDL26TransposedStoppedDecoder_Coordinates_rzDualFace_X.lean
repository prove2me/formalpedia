-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rzDualFace_X
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rzDualFace_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:46:11.281045+00:00
-- url     : https://prove2.me/theorems/571a349e-649e-4fc9-9f64-d023d47e1fd4
-- title:
--   Coordinates: rz Dual Face X
-- statement:
--   The opposite direction uses the original actual RZ admissibility data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L281-L305
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L281-L305

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rzDualFace_X (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (f : RZFace P S) :
    rxFaceX (transposePresentation P) S (rzDualFace P S f) =
      rzDualX P S (rzFaceZ P A S f) := by sorry
