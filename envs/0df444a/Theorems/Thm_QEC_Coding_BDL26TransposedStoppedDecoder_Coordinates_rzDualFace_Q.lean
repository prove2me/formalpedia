-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rzDualFace_Q
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rzDualFace_Q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:22:44.015887+00:00
-- url     : https://prove2.me/theorems/4ada2855-8bee-487a-afec-f14b7741ed9f
-- title:
--   Coordinates: rz Dual Face Q
-- statement:
--   The Coordinates construction uses the rz Dual Face Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L313-L329
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L313-L329

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rzDualFace_Q (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (f : RZFace P S) (b : Two) :
    rxFaceQ (transposePresentation P) S (rzDualFace P S f) b =
      rzDualQ P S (rzFaceQ P A S f b) := by sorry
