-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_coboundary1_transport
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.coboundary1_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:22:21.329174+00:00
-- url     : https://prove2.me/theorems/e89e8d6c-9d19-4651-89f2-ca3b60c55584
-- title:
--   Coordinates: coboundary1 transport
-- statement:
--   Finite coordinate transport of the actual degree-one Tanner map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L119-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L119-L131

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.coboundary1_transport (P R : TannerSquarePresentation)
    (eQ : P.Q ≃ R.Q) (eZ : P.Z ≃ R.Z)
    (h : ∀ q z, R.qz (eQ q) (eZ z) = P.qz q z)
    (w : Word BDL26Field P.Q) (z : P.Z) :
    tannerCoboundary1 R (wordEquiv eQ w) (eZ z) =
      tannerCoboundary1 P w z := by sorry
