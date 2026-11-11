-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_xq_of_face_equiv
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.xq_of_face_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:22:13.580933+00:00
-- url     : https://prove2.me/theorems/8d1dd3f3-7fbf-4311-b261-38d64ec1254f
-- title:
--   Coordinates: xq of face equiv
-- statement:
--   Primitive face equations derive X-Q incidence conjugacy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L66-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L66-L82

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.xq_of_face_equiv (P R : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (B : TannerSquareAdmissible R)
    (eX : P.X ≃ R.X) (eQ : P.Q ≃ R.Q) (eF : P.Face ≃ R.Face)
    (hX : ∀ f, R.faceX (eF f) = eX (P.faceX f))
    (hQ : ∀ f b, R.faceQ (eF f) b = eQ (P.faceQ f b))
    (x : P.X) (q : P.Q) : R.xq (eX x) (eQ q) = P.xq x q := by sorry
