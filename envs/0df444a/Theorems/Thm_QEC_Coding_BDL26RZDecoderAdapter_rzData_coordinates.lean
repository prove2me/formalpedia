-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzData_coordinates
-- name    : QEC.Coding.BDL26RZDecoderAdapter.rzData_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:57:12.708082+00:00
-- url     : https://prove2.me/theorems/8f621ec1-190d-4dac-b323-991b5ed11f10
-- title:
--   BDL26 RZDecoder Adapter: rz Data coordinates
-- statement:
--   The indexed regions and projection are the actual constructor objects,
--   with only the defining upper-carrier transport.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L301-L313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L301-L313

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

theorem QEC.Coding.BDL26RZDecoderAdapter.rzData_coordinates (h : ¬i.val % 2 = 0) :
    HEq (rzData S depth i h).coarseRegion
      (blockRegion (state S i.val).presentation S) ∧
    HEq (rzData S depth i h).correctionRegion
      (BDL26RZSupportedBoundary.correctionRegion (state S i.val).presentation S) ∧
    HEq (rzData S depth i h).correctionOwner
      (blockCorrectionOwner (state S i.val).presentation S) ∧
    HEq (rzData S depth i h).induced.correctionProjection
      (rzQParity (state S i.val).presentation S) := by sorry
