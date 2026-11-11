-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzData_map2_active_owner
-- name    : QEC.Coding.BDL26RZDecoderAdapter.rzData_map2_active_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:27:37.001768+00:00
-- url     : https://prove2.me/theorems/a7b6a392-8149-4fde-9687-8fa4f24c706f
-- title:
--   BDL26 RZDecoder Adapter: rz Data map2 active owner
-- statement:
--   A nonzero selected image retains a nonzero input at its actual block owner.
--   This follows from the actual root lift before transporting the upper carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L328-L350
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L328-L350

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

theorem QEC.Coding.BDL26RZDecoderAdapter.rzData_map2_active_owner (h : ¬i.val % 2 = 0)
    (s : Word BDL26Field (FamilyZ S depth i.castSucc))
    (p : FamilyZ S depth i.succ)
    (hp : ((indexedDecoderData S depth).selectedMap i).map2 s p ≠ 0) :
    ∃ z, (rzData S depth i h).topCenter p = Vertex.z z ∧ s z ≠ 0 := by sorry
