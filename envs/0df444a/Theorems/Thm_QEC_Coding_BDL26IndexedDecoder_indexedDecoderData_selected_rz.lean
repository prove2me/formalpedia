-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_indexedDecoderData_selected_rz
-- name    : QEC.Coding.BDL26IndexedDecoder.indexedDecoderData_selected_rz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:52:58.915282+00:00
-- url     : https://prove2.me/theorems/922981e5-29f5-4b8b-b85f-544cc47f81d4
-- title:
--   BDL26 Indexed Decoder: indexed Decoder Data selected rz
-- statement:
--   All degrees of the selected odd-lower-index map are the actual RZ maps.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/IndexedDecoder.lean#L121-L132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/IndexedDecoder.lean#L121-L132

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

theorem QEC.Coding.BDL26IndexedDecoder.indexedDecoderData_selected_rz (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : ¬i.val % 2 = 0) :
    HEq ((indexedDecoderData S depth).selectedMap i).map0
      (rzCochainMap (state S i.val).presentation (state S i.val).admissible S).map0 ∧
    HEq ((indexedDecoderData S depth).selectedMap i).map1
      (rzCochainMap (state S i.val).presentation (state S i.val).admissible S).map1 ∧
    HEq ((indexedDecoderData S depth).selectedMap i).map2
      (rzCochainMap (state S i.val).presentation (state S i.val).admissible S).map2 := by sorry
