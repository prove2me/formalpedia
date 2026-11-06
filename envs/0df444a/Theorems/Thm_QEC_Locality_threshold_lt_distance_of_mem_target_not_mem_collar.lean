-- Prove2me | Theorems.Thm_QEC_Locality_threshold_lt_distance_of_mem_target_not_mem_collar
-- name    : QEC.Locality.threshold_lt_distance_of_mem_target_not_mem_collar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:04:08.525125+00:00
-- url     : https://prove2.me/theorems/ffa75cee-ac89-49f8-b49b-c8e77d28eb54
-- title:
--   Locality: threshold lt distance of mem target not mem collar
-- statement:
--   Leaving the target together with its one-threshold collar forces a
--   strictly threshold-long geometric separation from every point in the target.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1122-L1179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1122-L1179

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableRecursive

theorem QEC.Locality.threshold_lt_distance_of_mem_target_not_mem_collar
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ)
    {p q : ι}
    (hp : p ∈ centeredRectangleQubits embedding center
      outerHorizontalRadius outerVerticalRadius)
    (hq : q ∉ centeredRectangleQubits embedding center
      (outerHorizontalRadius + threshold) (outerVerticalRadius + threshold)) :
    threshold < embedding.distance p q := by sorry
