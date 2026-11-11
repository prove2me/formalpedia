-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_delta1_coordinates
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.delta1_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:50:06.860446+00:00
-- url     : https://prove2.me/theorems/3788638f-c3a7-4533-9dd5-e1fcaa350306
-- title:
--   BDL26 RZFinite Block Transport: delta1 coordinates
-- statement:
--   The BDL26 RZFinite Block Transport construction uses the delta1 coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L516-L520
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L516-L520

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

theorem QEC.Coding.BDL26RZFiniteBlockTransport.delta1_coordinates (w : Upper S depth i) :
    read2 S depth i odd ((indexedFamily S depth).coboundary1 i.succ w)=
      rzCoboundary1 (Old S depth i) (state S i.val).admissible S (read1 S depth i odd w) := by sorry
