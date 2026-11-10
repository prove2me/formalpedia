-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_indexedDecoderData_selected_rx
-- name    : QEC.Coding.BDL26IndexedDecoder.indexedDecoderData_selected_rx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:08:59.519172+00:00
-- url     : https://prove2.me/theorems/e97a8068-db4a-477d-a0f6-49e0f663749c
-- title:
--   BDL26 Indexed Decoder: indexed Decoder Data selected rx
-- statement:
--   All degrees of the selected even-lower-index map are the actual RX maps.
--   Heterogeneous equality records only the defining successor-carrier transport.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/IndexedDecoder.lean#L106-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/IndexedDecoder.lean#L106-L117

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

theorem QEC.Coding.BDL26IndexedDecoder.indexedDecoderData_selected_rx (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : i.val % 2 = 0) :
    HEq ((indexedDecoderData S depth).selectedMap i).map0
      (rxMap (state S i.val).presentation S).map0 ∧
    HEq ((indexedDecoderData S depth).selectedMap i).map1
      (rxMap (state S i.val).presentation S).map1 ∧
    HEq ((indexedDecoderData S depth).selectedMap i).map2
      (rxMap (state S i.val).presentation S).map2 := by sorry
