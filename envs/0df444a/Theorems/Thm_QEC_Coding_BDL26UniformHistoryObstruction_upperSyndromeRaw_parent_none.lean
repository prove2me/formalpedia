-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_upperSyndromeRaw_parent_none
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.upperSyndromeRaw_parent_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:38:06.03958+00:00
-- url     : https://prove2.me/theorems/572b54da-0104-468f-b259-47d8b6bf16ec
-- title:
--   BDL26 Uniform History Obstruction: upper Syndrome Raw parent none
-- statement:
--   All nonzero upper syndrome owners are unparented in the unchanged intrinsic graph.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWitness.lean#L121-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWitness.lean#L121-L138

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks
open BDL26OwnerParentObstruction BDL26ReplacementSupport BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26XLocalRadialParity BDL26XLocalConnectingWeight
open MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26UniformHistoryObstruction.upperSyndromeRaw_parent_none (S : OddScale) (n : Nat)
    (target : RZZ (rxReplacementPresentation (state S n).presentation S) S)
    (h : (upperSyndromeRaw S n) target ≠ 0) :
    rxParent (state S n).presentation S
      (.z (rzSyndromeOwner (rxReplacementPresentation (state S n).presentation S)
        S target)) = none := by sorry
