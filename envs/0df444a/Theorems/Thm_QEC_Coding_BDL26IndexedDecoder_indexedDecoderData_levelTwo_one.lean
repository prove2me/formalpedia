-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_indexedDecoderData_levelTwo_one
-- name    : QEC.Coding.BDL26IndexedDecoder.indexedDecoderData_levelTwo_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:31:20.844049+00:00
-- url     : https://prove2.me/theorems/14e69ccd-0fc0-427e-ac17-4b1980eee773
-- title:
--   BDL26 Indexed Decoder: indexed Decoder Data level Two one
-- statement:
--   All three second-edge maps agree with the physical-C₂ adapter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/IndexedDecoder.lean#L94-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/IndexedDecoder.lean#L94-L102

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

theorem QEC.Coding.BDL26IndexedDecoder.indexedDecoderData_levelTwo_one (S : OddScale) :
    ((indexedDecoderData S 2).selectedMap (1 : StepIndex 2)).map0 =
      ((BDL26LevelTwoDecoder.decoderData S).selectedMap (1 : StepIndex 2)).map0 ∧
    ((indexedDecoderData S 2).selectedMap (1 : StepIndex 2)).map1 =
      ((BDL26LevelTwoDecoder.decoderData S).selectedMap (1 : StepIndex 2)).map1 ∧
    ((indexedDecoderData S 2).selectedMap (1 : StepIndex 2)).map2 =
      ((BDL26LevelTwoDecoder.decoderData S).selectedMap (1 : StepIndex 2)).map2 := by sorry
