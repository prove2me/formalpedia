-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzStepOutput_relation
-- name    : QEC.Coding.BDL26RZDecoderAdapter.rzStepOutput_relation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:27:48.678194+00:00
-- url     : https://prove2.me/theorems/fcde9027-3803-48d9-a7fa-d3512e5d206a
-- title:
--   BDL26 RZDecoder Adapter: rz Step Output relation
-- statement:
--   The BDL26 RZDecoder Adapter construction uses the rz Step Output relation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L413-L419
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L413-L419

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZSupportedBoundary
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementSupport BDL26RZConcreteParity BDL26LevelTwoDistance
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open BDL26AlternatingCochain BDL26ReplacementCochainMaps
open scoped Classical BigOperators
universe u
attribute [local instance] QEC.Coding.BDL26RZDecoderAdapter.rzQDecEq
attribute [local instance] QEC.Coding.BDL26RZDecoderAdapter.rzZDecEq
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RZDecoderAdapter.rzStepOutput_relation (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    sigma.val = (indexedFamily S depth).coboundary1 i.succ
      (rzStepOutput S depth i h sigma).correction +
      ((indexedDecoderData S depth).selectedMap i).map2
        (rzStepOutput S depth i h sigma).coarse.val := by sorry
