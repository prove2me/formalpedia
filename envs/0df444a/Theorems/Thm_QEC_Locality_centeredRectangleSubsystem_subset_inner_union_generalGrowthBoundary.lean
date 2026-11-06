-- Prove2me | Theorems.Thm_QEC_Locality_centeredRectangleSubsystem_subset_inner_union_generalGrowthBoundary
-- name    : QEC.Locality.centeredRectangleSubsystem_subset_inner_union_generalGrowthBoundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:04:47.797884+00:00
-- url     : https://prove2.me/theorems/11a04fca-5700-48f6-9f7f-885011baa769
-- title:
--   Locality: centered Rectangle Subsystem subset inner union general Growth Boundary
-- statement:
--   The target rectangle is selected by the previous rectangle and the
--   computed general boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1228-L1246
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1228-L1246

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

theorem QEC.Locality.centeredRectangleSubsystem_subset_inner_union_generalGrowthBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold : ℝ) :
    (centeredRectangleSubsystem embedding center outerHorizontalRadius
      outerVerticalRadius).selected ⊆
      (unionSubsystem
        (centeredRectangleSubsystem embedding center innerHorizontalRadius innerVerticalRadius)
        (centeredRectangleGeneralGrowthBoundary P embedding center
          innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
          outerVerticalRadius threshold)).selected := by sorry
