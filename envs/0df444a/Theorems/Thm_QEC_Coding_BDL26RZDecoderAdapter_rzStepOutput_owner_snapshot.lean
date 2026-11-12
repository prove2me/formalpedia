-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzStepOutput_owner_snapshot
-- name    : QEC.Coding.BDL26RZDecoderAdapter.rzStepOutput_owner_snapshot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:17:09.041195+00:00
-- url     : https://prove2.me/theorems/be13ba20-f3e3-4ae6-9ede-eb3d6f5fc142
-- title:
--   BDL26 RZDecoder Adapter: rz Step Output owner snapshot
-- statement:
--   The recorded labels refer to exactly these proved support snapshots.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L519-L528
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L519-L528

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

theorem QEC.Coding.BDL26RZDecoderAdapter.rzStepOutput_owner_snapshot (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (j : Fin (rzStepOutput S depth i h sigma).localComponents.length) :
    ((rzStepOutput_ownerLabels S depth i h sigma).label j).owner =
        some (.z (componentOwner S depth i h sigma j)) ∧
    ((rzStepOutput_ownerLabels S depth i h sigma).label j).correctionSupport =
        (rzStepOutput S depth i h sigma).componentSupportAt j ∧
    ((rzStepOutput_ownerLabels S depth i h sigma).label j).coboundarySupport =
        hammingSupport ((rzStepOutput S depth i h sigma).componentCoboundaryAt j) := by sorry
