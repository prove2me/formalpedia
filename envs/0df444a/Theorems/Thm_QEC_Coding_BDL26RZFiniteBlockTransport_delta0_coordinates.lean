-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_delta0_coordinates
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.delta0_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:34:32.268898+00:00
-- url     : https://prove2.me/theorems/0d457544-d730-4d27-b9f3-d70f7cfe0853
-- title:
--   BDL26 RZFinite Block Transport: delta0 coordinates
-- statement:
--   The BDL26 RZFinite Block Transport construction uses the delta0 coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L510-L514
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L510-L514

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

theorem QEC.Coding.BDL26RZFiniteBlockTransport.delta0_coordinates (p : Potential S depth i) :
    read1 S depth i odd ((indexedFamily S depth).coboundary0 i.succ p)=
      rzCoboundary0 (Old S depth i) (state S i.val).admissible S (read0 S depth i odd p) := by sorry
