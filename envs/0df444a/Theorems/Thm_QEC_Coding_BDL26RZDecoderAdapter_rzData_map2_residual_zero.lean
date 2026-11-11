-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzData_map2_residual_zero
-- name    : QEC.Coding.BDL26RZDecoderAdapter.rzData_map2_residual_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:28:48.458789+00:00
-- url     : https://prove2.me/theorems/93f3cc61-9247-4825-81db-c074d2f8858b
-- title:
--   BDL26 RZDecoder Adapter: rz Data map2 residual zero
-- statement:
--   Zero residual on a selected image is proved before discussing its selector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L548-L564
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L548-L564

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

theorem QEC.Coding.BDL26RZDecoderAdapter.rzData_map2_residual_zero (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Cochain2 i.castSucc)
    (z : (state S i.val).presentation.Z) :
    localResidual (rzData S depth i h) z
      (((indexedDecoderData S depth).selectedMap i).map2 sigma) = 0 := by sorry
