-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_lowerError_delta
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.lowerError_delta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:50:29.800309+00:00
-- url     : https://prove2.me/theorems/07418b81-fa05-4767-8415-e1aab89e6c95
-- title:
--   BDL26 RZFinite Block Transport: lower Error delta
-- statement:
--   The lower syndrome is derived from the original actual F09 calculation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L564-L577
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L564-L577

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

theorem QEC.Coding.BDL26RZFiniteBlockTransport.lowerError_delta (a b : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.castSucc (lowerError S depth i odd a b)=
      (run S depth i odd a).coarse.val+(run S depth i odd b).coarse.val := by sorry
