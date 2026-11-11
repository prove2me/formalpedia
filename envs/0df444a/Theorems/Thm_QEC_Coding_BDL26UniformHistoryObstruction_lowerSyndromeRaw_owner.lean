-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_lowerSyndromeRaw_owner
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.lowerSyndromeRaw_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:36:03.981199+00:00
-- url     : https://prove2.me/theorems/577ab328-ee8a-455e-b9d4-22a5b0d649d2
-- title:
--   BDL26 Uniform History Obstruction: lower Syndrome Raw owner
-- statement:
--   Every lower nonzero syndrome coordinate has the same genuine local owner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWitness.lean#L87-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWitness.lean#L87-L94

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

theorem QEC.Coding.BDL26UniformHistoryObstruction.lowerSyndromeRaw_owner (S : OddScale) (n : Nat) (z : RX2 (state S n).presentation S)
    (hz : (lowerSyndromeRaw S n) z ≠ 0) :
    rxSyndromeOwner (state S n).presentation S z = .x (retainedX S n) := by sorry
