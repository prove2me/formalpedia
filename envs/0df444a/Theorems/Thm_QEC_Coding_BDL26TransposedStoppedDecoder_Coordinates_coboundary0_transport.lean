-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_coboundary0_transport
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.coboundary0_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:21:49.910831+00:00
-- url     : https://prove2.me/theorems/f1d9289b-cfea-4d46-8719-44c130c77df6
-- title:
--   Coordinates: coboundary0 transport
-- statement:
--   Finite coordinate transport of the actual degree-zero Tanner map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L104-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L104-L116

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.coboundary0_transport (P R : TannerSquarePresentation)
    (eX : P.X ≃ R.X) (eQ : P.Q ≃ R.Q)
    (h : ∀ x q, R.xq (eX x) (eQ q) = P.xq x q)
    (w : Word BDL26Field P.X) (q : P.Q) :
    tannerCoboundary0 R (wordEquiv eX w) (eQ q) =
      tannerCoboundary0 P w q := by sorry
