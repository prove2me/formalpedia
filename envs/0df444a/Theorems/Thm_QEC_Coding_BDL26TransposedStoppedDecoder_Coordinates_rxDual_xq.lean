-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rxDual_xq
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rxDual_xq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:46:55.375936+00:00
-- url     : https://prove2.me/theorems/e220c618-9c67-4451-abbb-2439be0a7060
-- title:
--   Coordinates: rx Dual xq
-- statement:
--   Actual RX successor incidence, with both admissibilities derived.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L333-L344
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L333-L344

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rxDual_xq (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (x : (transposePresentation (rxReplacementPresentation P S)).X) (q : (transposePresentation (rxReplacementPresentation P S)).Q) :
    (rzReplacementPresentation (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S).xq (rxDualX P S x) (rxDualQ P S q) = (transposePresentation (rxReplacementPresentation P S)).xq x q := by sorry
