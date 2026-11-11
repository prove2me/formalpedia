-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_map2_coordinates
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.map2_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:34:37.682089+00:00
-- url     : https://prove2.me/theorems/f5722a47-2e6e-4bd7-86c0-f38735a5e63b
-- title:
--   BDL26 RZFinite Block Transport: map2 coordinates
-- statement:
--   The BDL26 RZFinite Block Transport construction uses the map2 coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L681-L684
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L681-L684

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZFiniteBlockTransport
open BDL26FiniteAlternatingCore
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26ReplacementCochainMaps BDL26LevelTwoDistance BDL26IndexedDecoder
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open scoped BigOperators Classical
open BDL26RZDecoderAdapter BDL26RZErrorPullback
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val % 2=0)

theorem QEC.Coding.BDL26RZFiniteBlockTransport.map2_coordinates (w : (indexedFamily S depth).Cochain2 i.castSucc) :
    read2 S depth i odd (((indexedDecoderData S depth).selectedMap i).map2 w)=
      map2Coord (Old S depth i) (state S i.val).admissible S w := by sorry
