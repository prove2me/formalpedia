-- Prove2me | Theorems.Thm_QEC_Locality_threshold_lt_distance_of_mem_inner_not_mem_outer
-- name    : QEC.Locality.threshold_lt_distance_of_mem_inner_not_mem_outer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:04:50.634077+00:00
-- url     : https://prove2.me/theorems/5699411f-885f-4ee7-80b4-1de63c44c17d
-- title:
--   Locality: threshold lt distance of mem inner not mem outer
-- statement:
--   Leaving the one-threshold enlarged square forces Euclidean distance above the threshold.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L322-L370
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L322-L370

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

theorem QEC.Locality.threshold_lt_distance_of_mem_inner_not_mem_outer
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerRadius threshold : ℝ)
    {p q : ι}
    (hp : p ∈ squareQubits embedding center (outerRadius - threshold))
    (hq : q ∉ squareQubits embedding center outerRadius) :
    threshold < embedding.distance p q := by sorry
