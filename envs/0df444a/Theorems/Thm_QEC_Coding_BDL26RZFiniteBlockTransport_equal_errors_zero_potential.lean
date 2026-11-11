-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_equal_errors_zero_potential
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.equal_errors_zero_potential
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:16:24.771146+00:00
-- url     : https://prove2.me/theorems/b61cb61b-d58f-4e2d-b205-6cda80725d70
-- title:
--   BDL26 RZFinite Block Transport: equal errors zero potential
-- statement:
--   The BDL26 RZFinite Block Transport construction uses the equal errors zero potential property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L967-L973
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L967-L973

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

theorem QEC.Coding.BDL26RZFiniteBlockTransport.equal_errors_zero_potential (a : Upper S depth i) :
    Pullback S depth i odd ∅ ∅ a a 0 := by sorry
