-- Prove2me | Theorems.Thm_QEC_Locality_squareSubsystem_subset_inner_union_growthBoundary
-- name    : QEC.Locality.squareSubsystem_subset_inner_union_growthBoundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:03:23.768653+00:00
-- url     : https://prove2.me/theorems/2b21a243-77c3-459e-a4e0-9023605c14a3
-- title:
--   Locality: square Subsystem subset inner union growth Boundary
-- statement:
--   The enlarged square lies in the union of the inner square and its computed boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L403-L415
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L403-L415

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

theorem QEC.Locality.squareSubsystem_subset_inner_union_growthBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerRadius threshold : ℝ) :
    (squareSubsystem embedding center outerRadius).selected ⊆
      (unionSubsystem
        (squareSubsystem embedding center (outerRadius - threshold))
        (squareGrowthBoundary P embedding center outerRadius threshold)).selected := by sorry
