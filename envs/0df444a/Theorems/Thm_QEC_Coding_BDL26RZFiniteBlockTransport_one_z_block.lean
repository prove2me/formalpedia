-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_one_z_block
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.one_z_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:20:20.225283+00:00
-- url     : https://prove2.me/theorems/bb8f0a73-efc9-4809-bc16-702b7d44a9a7
-- title:
--   BDL26 RZFinite Block Transport: one z block
-- statement:
--   Z-local error differences are locally exact after the ORIGINAL two corrections.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L916-L931
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L916-L931

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

theorem QEC.Coding.BDL26RZFiniteBlockTransport.one_z_block (above : 2 ≤ i.val) (z : (Old S depth i).Z)
    (a b : Upper S depth i) (he : hammingSupport (a+b) ⊆ zBlocks S depth i odd {z}) :
    ∃ p : Potential S depth i, Pullback S depth i odd ∅ {z} a b p ∧
      lowerError S depth i odd a b=0 ∧
      (run S depth i odd a).coarse.val=(run S depth i odd b).coarse.val ∧
      updated S depth i odd a b=(indexedFamily S depth).coboundary0 i.succ p := by sorry
