-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxCorrection_partition
-- name    : QEC.Coding.BDL26ReplacementSupport.rxCorrection_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:56:27.387872+00:00
-- url     : https://prove2.me/theorems/5eb447f0-9104-4d4e-9c67-240791e12dac
-- title:
--   BDL26 Replacement Support: rx Correction partition
-- statement:
--   The BDL26 Replacement Support construction uses the rx Correction partition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L113-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L113-L117

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped BigOperators Classical

theorem QEC.Coding.BDL26ReplacementSupport.rxCorrection_partition (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RX1 P S)) :
    (∑ v : Vertex P, fiberPart (rxCorrectionOwner P S) v word) = word := by sorry
