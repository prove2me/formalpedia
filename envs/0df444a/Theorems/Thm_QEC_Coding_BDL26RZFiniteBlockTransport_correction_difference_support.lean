-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_correction_difference_support
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.correction_difference_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:49:56.016676+00:00
-- url     : https://prove2.me/theorems/231020c6-a672-4387-a51e-77df9f32ce4a
-- title:
--   BDL26 RZFinite Block Transport: correction difference support
-- statement:
--   Unaffected original residuals, hence their original chosen corrections, agree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L620-L665
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L620-L665

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

theorem QEC.Coding.BDL26RZFiniteBlockTransport.correction_difference_support (Q0 : Finset (Old S depth i).Q)
    (Z0 : Finset (Old S depth i).Z) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ inputBlocks S depth i odd Q0 Z0) :
    hammingSupport ((run S depth i odd a).correction+(run S depth i odd b).correction) ⊆
      zBlocks S depth i odd (Coordinates.zplus (Old S depth i) Q0 Z0) := by sorry
