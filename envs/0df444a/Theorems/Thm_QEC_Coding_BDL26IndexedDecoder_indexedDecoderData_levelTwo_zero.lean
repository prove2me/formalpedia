-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_indexedDecoderData_levelTwo_zero
-- name    : QEC.Coding.BDL26IndexedDecoder.indexedDecoderData_levelTwo_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:31:30.916967+00:00
-- url     : https://prove2.me/theorems/c5507112-4c4a-44f5-b4d5-b6cd6c94855b
-- title:
--   BDL26 Indexed Decoder: indexed Decoder Data level Two zero
-- statement:
--   All three first-edge maps are the concrete RX maps, not zero fillers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/IndexedDecoder.lean#L83-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/IndexedDecoder.lean#L83-L91

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

theorem QEC.Coding.BDL26IndexedDecoder.indexedDecoderData_levelTwo_zero (S : OddScale) :
    ((indexedDecoderData S 2).selectedMap (0 : StepIndex 2)).map0 =
      (rxMap baseTannerSquarePresentation S).map0 ∧
    ((indexedDecoderData S 2).selectedMap (0 : StepIndex 2)).map1 =
      (rxMap baseTannerSquarePresentation S).map1 ∧
    ((indexedDecoderData S 2).selectedMap (0 : StepIndex 2)).map2 =
      (rxMap baseTannerSquarePresentation S).map2 := by sorry
