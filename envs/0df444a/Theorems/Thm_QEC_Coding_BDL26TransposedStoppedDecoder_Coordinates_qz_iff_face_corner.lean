-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_qz_iff_face_corner
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.qz_iff_face_corner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:45:08.391387+00:00
-- url     : https://prove2.me/theorems/95c601be-fe66-47c5-8414-1e1b02787536
-- title:
--   Coordinates: qz iff face corner
-- statement:
--   Actual Q-Z incidence is recovered from an ordered face corner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L50-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L50-L63

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.qz_iff_face_corner (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z) :
    P.qz q z = true ↔
      ∃ f : P.Face, ∃ b : Two, P.faceZ f = z ∧ P.faceQ f b = q := by sorry
