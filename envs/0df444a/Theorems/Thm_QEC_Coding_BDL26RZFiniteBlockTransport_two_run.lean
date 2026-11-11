-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_two_run
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.two_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T10:49:32.097214+00:00
-- url     : https://prove2.me/theorems/ad210207-e375-48e6-9b26-cd44c5ad3a2a
-- title:
--   BDL26 RZFinite Block Transport: two run
-- statement:
--   Complete actual two-run result: no filling, residual or lower preimage is supplied.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L764-L857
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L764-L857

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_two_run

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

theorem QEC.Coding.BDL26RZFiniteBlockTransport.two_run (_above : 2 ≤ i.val) (Q0 : Finset (Old S depth i).Q)
    (Z0 : Finset (Old S depth i).Z) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ inputBlocks S depth i odd Q0 Z0) :
    ∃ p : Potential S depth i, Pullback S depth i odd Q0 Z0 a b p := by sorry
