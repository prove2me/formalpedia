-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzData_topCenter_is_z
-- name    : QEC.Coding.BDL26RZDecoderAdapter.rzData_topCenter_is_z
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:57:38.233199+00:00
-- url     : https://prove2.me/theorems/224e699d-87a9-4136-8afa-fd640f9f0152
-- title:
--   BDL26 RZDecoder Adapter: rz Data top Center is z
-- statement:
--   Every indexed syndrome coordinate has its actual Z-block owner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L316-L324
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L316-L324

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

theorem QEC.Coding.BDL26RZDecoderAdapter.rzData_topCenter_is_z (h : ¬i.val % 2 = 0)
    (p : FamilyZ S depth i.succ) :
    ∃ z, (rzData S depth i h).topCenter p = Vertex.z z := by sorry
