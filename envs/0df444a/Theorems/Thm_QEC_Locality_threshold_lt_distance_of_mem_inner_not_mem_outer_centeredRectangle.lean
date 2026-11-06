-- Prove2me | Theorems.Thm_QEC_Locality_threshold_lt_distance_of_mem_inner_not_mem_outer_centeredRectangle
-- name    : QEC.Locality.threshold_lt_distance_of_mem_inner_not_mem_outer_centeredRectangle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:03:59.743508+00:00
-- url     : https://prove2.me/theorems/16953f70-71fc-438e-96a5-390ebfea3650
-- title:
--   Locality: threshold lt distance of mem inner not mem outer centered Rectangle
-- statement:
--   Leaving the simultaneously enlarged rectangle forces Euclidean distance
--   strictly above the common growth threshold.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L857-L909
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L857-L909

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

theorem QEC.Locality.threshold_lt_distance_of_mem_inner_not_mem_outer_centeredRectangle
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ)
    {p q : ι}
    (hp : p ∈ centeredRectangleQubits embedding center
      (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold))
    (hq : q ∉ centeredRectangleQubits embedding center
      outerHorizontalRadius outerVerticalRadius) :
    threshold < embedding.distance p q := by sorry
