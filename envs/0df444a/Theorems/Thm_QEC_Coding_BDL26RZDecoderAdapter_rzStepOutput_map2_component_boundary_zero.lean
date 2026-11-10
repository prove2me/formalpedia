-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzStepOutput_map2_component_boundary_zero
-- name    : QEC.Coding.BDL26RZDecoderAdapter.rzStepOutput_map2_component_boundary_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:58:39.473895+00:00
-- url     : https://prove2.me/theorems/0b33d795-2e2b-4ede-b03c-ed6d4dde17ad
-- title:
--   BDL26 RZDecoder Adapter: rz Step Output map2 component boundary zero
-- statement:
--   The canonical selector may return a cycle; its coboundary is zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L567-L575
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L567-L575

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

theorem QEC.Coding.BDL26RZDecoderAdapter.rzStepOutput_map2_component_boundary_zero (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.castSucc)
    (j : Fin (rzStepOutput S depth i h
      (embeddedSyndrome S depth i sigma)).localComponents.length) :
    (rzStepOutput S depth i h (embeddedSyndrome S depth i sigma)).componentCoboundaryAt j = 0 := by sorry
