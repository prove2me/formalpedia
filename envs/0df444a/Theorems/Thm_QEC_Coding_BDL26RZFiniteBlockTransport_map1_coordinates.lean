-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_map1_coordinates
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.map1_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:34:12.779319+00:00
-- url     : https://prove2.me/theorems/4b5151ab-d6e7-48e8-b61b-f5bf66ee36d8
-- title:
--   BDL26 RZFinite Block Transport: map1 coordinates
-- statement:
--   The BDL26 RZFinite Block Transport construction uses the map1 coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L522-L525
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L522-L525

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

theorem QEC.Coding.BDL26RZFiniteBlockTransport.map1_coordinates (w : Lower S depth i) :
    read1 S depth i odd (((indexedDecoderData S depth).selectedMap i).map1 w)=
      map1Coord (Old S depth i) (state S i.val).admissible S w := by sorry
