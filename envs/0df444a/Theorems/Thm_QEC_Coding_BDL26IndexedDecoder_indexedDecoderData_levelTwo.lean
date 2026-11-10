-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_indexedDecoderData_levelTwo
-- name    : QEC.Coding.BDL26IndexedDecoder.indexedDecoderData_levelTwo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:32:01.966895+00:00
-- url     : https://prove2.me/theorems/bc0c36d0-c273-4d6d-b0f9-e798321eb2f3
-- title:
--   BDL26 Indexed Decoder: indexed Decoder Data level Two
-- statement:
--   Every selected degree map agrees with the accepted depth-two decoder.
--   This compares the mathematical maps rather than opaque proof-bearing records.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/IndexedDecoder.lean#L137-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/IndexedDecoder.lean#L137-L144

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26IndexedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26ReplacementCochainMaps BDL26RZLocalReplacement BDL26RXLocalReplacement
open BDL26RZMap1CoordinateBridge
open MultiscaleDecoder BDL26AlternatingCochain
open scoped Classical
universe u

theorem QEC.Coding.BDL26IndexedDecoder.indexedDecoderData_levelTwo (S : OddScale) (i : StepIndex 2) :
    ((indexedDecoderData S 2).selectedMap i).map0 =
      ((BDL26LevelTwoDecoder.decoderData S).selectedMap i).map0 ∧
    ((indexedDecoderData S 2).selectedMap i).map1 =
      ((BDL26LevelTwoDecoder.decoderData S).selectedMap i).map1 ∧
    ((indexedDecoderData S 2).selectedMap i).map2 =
      ((BDL26LevelTwoDecoder.decoderData S).selectedMap i).map2 := by sorry
