-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_qz_of_face_equiv
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.qz_of_face_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:23:41.470517+00:00
-- url     : https://prove2.me/theorems/8bc6a72c-c5d3-4133-9110-8fd37fb17008
-- title:
--   Coordinates: qz of face equiv
-- statement:
--   Primitive face equations derive Q-Z incidence conjugacy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L85-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L85-L101

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.qz_of_face_equiv (P R : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (B : TannerSquareAdmissible R)
    (eQ : P.Q ≃ R.Q) (eZ : P.Z ≃ R.Z) (eF : P.Face ≃ R.Face)
    (hZ : ∀ f, R.faceZ (eF f) = eZ (P.faceZ f))
    (hQ : ∀ f b, R.faceQ (eF f) b = eQ (P.faceQ f b))
    (q : P.Q) (z : P.Z) : R.qz (eQ q) (eZ z) = P.qz q z := by sorry
