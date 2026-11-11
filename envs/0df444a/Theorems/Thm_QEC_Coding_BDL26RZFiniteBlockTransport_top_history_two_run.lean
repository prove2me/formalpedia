-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_top_history_two_run
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.top_history_two_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:20:29.934147+00:00
-- url     : https://prove2.me/theorems/cc4a1192-12d3-4a44-84ef-1b04207c63e6
-- title:
--   BDL26 RZFinite Block Transport: top history two run
-- statement:
--   Both correction words below are literal snapshots of the original stopped histories.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L1005-L1022
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L1005-L1022

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
open BDL26OwnerIncidenceMasks BDL26CanonicalHistoryMarks

theorem QEC.Coding.BDL26RZFiniteBlockTransport.top_history_two_run (j : Nat)
    (Q0 : Finset (Old S (2*j+4) (topStep j)).Q)
    (Z0 : Finset (Old S (2*j+4) (topStep j)).Z)
    (a b : Upper S (2*j+4) (topStep j))
    (he : hammingSupport (a+b) ⊆ inputBlocks S (2*j+4) (topStep j) (topStep_odd j) Q0 Z0) :
    ∃ p : Potential S (2*j+4) (topStep j),
      Pullback S (2*j+4) (topStep j) (topStep_odd j) Q0 Z0 a b p ∧
      ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map1
        (lowerError S (2*j+4) (topStep j) (topStep_odd j) a b)=
        a+b+(topOutput S j a).correction+(topOutput S j b).correction+
          (indexedFamily S (2*j+4)).coboundary0 (topStep j).succ p ∧
      (indexedFamily S (2*j+4)).coboundary1 (topStep j).castSucc
        (lowerError S (2*j+4) (topStep j) (topStep_odd j) a b)=
        (topOutput S j a).coarse.val+(topOutput S j b).coarse.val := by sorry
