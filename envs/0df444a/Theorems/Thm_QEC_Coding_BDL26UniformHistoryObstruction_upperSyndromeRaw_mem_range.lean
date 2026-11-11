-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_upperSyndromeRaw_mem_range
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.upperSyndromeRaw_mem_range
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:36:28.994097+00:00
-- url     : https://prove2.me/theorems/cb6b4f04-6d99-49ef-8d57-dd088ea8f857
-- title:
--   BDL26 Uniform History Obstruction: upper Syndrome Raw mem range
-- statement:
--   The next image is a genuine upper coboundary by the proved cochain relation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWitness.lean#L97-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWitness.lean#L97-L103

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

theorem QEC.Coding.BDL26UniformHistoryObstruction.upperSyndromeRaw_mem_range (S : OddScale) (n : Nat) :
    (upperSyndromeRaw S n) ∈ LinearMap.range
      (rzCoboundary1 (rxReplacementPresentation (state S n).presentation S)
        (rxState S (state S n)).admissible S) := by sorry
