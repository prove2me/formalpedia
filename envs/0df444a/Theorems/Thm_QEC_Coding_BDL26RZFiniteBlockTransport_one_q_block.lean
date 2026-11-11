-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_one_q_block
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.one_q_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:37:44.526785+00:00
-- url     : https://prove2.me/theorems/83bb5be5-961f-4537-a3ad-cba0adcf0e62
-- title:
--   BDL26 RZFinite Block Transport: one q block
-- statement:
--   The BDL26 RZFinite Block Transport construction uses the one q block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L905-L909
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L905-L909

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

theorem QEC.Coding.BDL26RZFiniteBlockTransport.one_q_block (above : 2 ≤ i.val) (q : (Old S depth i).Q)
    (a b : Upper S depth i) (he : hammingSupport (a+b) ⊆ qBlocks S depth i odd {q}) :
    ∃ p : Potential S depth i, Pullback S depth i odd {q} ∅ a b p := by sorry
