-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzStepOutput_component_eq
-- name    : QEC.Coding.BDL26RZDecoderAdapter.rzStepOutput_component_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:57:48.512201+00:00
-- url     : https://prove2.me/theorems/693a1295-1da5-4319-b8ef-a7dca4a84a75
-- title:
--   BDL26 RZDecoder Adapter: rz Step Output component eq
-- statement:
--   The BDL26 RZDecoder Adapter construction uses the rz Step Output component eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L444-L458
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L444-L458

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

theorem QEC.Coding.BDL26RZDecoderAdapter.rzStepOutput_component_eq (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (j : Fin (rzStepOutput S depth i h sigma).localComponents.length) :
    (rzStepOutput S depth i h sigma).componentAt j =
      localCorrectionComponent (rzData S depth i h)
        (rzData_localTopCohomology S depth i h)
        (componentOwner S depth i h sigma j) sigma.val := by sorry
