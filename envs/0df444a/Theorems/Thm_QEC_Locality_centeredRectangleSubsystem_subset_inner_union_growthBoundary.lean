-- Prove2me | Theorems.Thm_QEC_Locality_centeredRectangleSubsystem_subset_inner_union_growthBoundary
-- name    : QEC.Locality.centeredRectangleSubsystem_subset_inner_union_growthBoundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:04:09.385259+00:00
-- url     : https://prove2.me/theorems/62325703-912a-469c-be00-4a1db9c9b9fd
-- title:
--   Locality: centered Rectangle Subsystem subset inner union growth Boundary
-- statement:
--   The grown rectangle is selected by the union of the prior rectangle and
--   the computed shell/crossing boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L948-L964
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L948-L964

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

theorem QEC.Locality.centeredRectangleSubsystem_subset_inner_union_growthBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ) :
    (centeredRectangleSubsystem embedding center outerHorizontalRadius
      outerVerticalRadius).selected ⊆
      (unionSubsystem
        (centeredRectangleSubsystem embedding center
          (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold))
        (centeredRectangleGrowthBoundary P embedding center outerHorizontalRadius
          outerVerticalRadius threshold)).selected := by sorry
