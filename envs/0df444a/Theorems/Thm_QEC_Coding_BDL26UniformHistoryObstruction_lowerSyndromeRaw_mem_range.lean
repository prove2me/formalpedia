-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_lowerSyndromeRaw_mem_range
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.lowerSyndromeRaw_mem_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:37:51.582126+00:00
-- url     : https://prove2.me/theorems/8f74fd0b-7644-4216-abea-0dfd9abf6023
-- title:
--   BDL26 Uniform History Obstruction: lower Syndrome Raw mem range
-- statement:
--   The input is a genuine coboundary, not an arbitrary basis cochain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWitness.lean#L56-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWitness.lean#L56-L59

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

theorem QEC.Coding.BDL26UniformHistoryObstruction.lowerSyndromeRaw_mem_range (S : OddScale) (n : Nat) :
    (lowerSyndromeRaw S n) ∈ LinearMap.range
      (tannerCoboundary1 (rxReplacementPresentation (state S n).presentation S)) := by sorry
