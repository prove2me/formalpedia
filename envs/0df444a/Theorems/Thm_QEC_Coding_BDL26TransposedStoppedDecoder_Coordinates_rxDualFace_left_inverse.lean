-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rxDualFace_left_inverse
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rxDualFace_left_inverse
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:59:33.094382+00:00
-- url     : https://prove2.me/theorems/2a9779c6-15c0-44e6-9ae3-26217ad09488
-- title:
--   Coordinates: rx Dual Face left inverse
-- statement:
--   The Coordinates construction uses the rx Dual Face left inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L190-L192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L190-L192

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rxDualFace_left_inverse (P : TannerSquarePresentation) (S : OddScale)
    (f : RXFace P S) : (rxDualFace P S).symm (rxDualFace P S f) = f := by sorry
