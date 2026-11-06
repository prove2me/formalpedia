-- Prove2me | Theorems.Thm_QEC_Locality_fixedGeneratorOuterBoundary_centeredRectangle_subset_growthBoundary
-- name    : QEC.Locality.fixedGeneratorOuterBoundary_centeredRectangle_subset_growthBoundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:04:30.295787+00:00
-- url     : https://prove2.me/theorems/c84474a9-c37a-47d0-af7e-6b44135bc8b5
-- title:
--   Locality: fixed Generator Outer Boundary centered Rectangle subset growth Boundary
-- statement:
--   The computed rectangle-growth boundary contains every actual
--   fixed-generator outer-boundary qubit of the inner rectangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L913-L944
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L913-L944

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

theorem QEC.Locality.fixedGeneratorOuterBoundary_centeredRectangle_subset_growthBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ) :
    P.fixedGeneratorOuterBoundary
        ((centeredRectangleSubsystem embedding center
          (outerHorizontalRadius - threshold)
          (outerVerticalRadius - threshold)).selected : Set ι) ⊆
      ((centeredRectangleGrowthBoundary P embedding center outerHorizontalRadius
        outerVerticalRadius threshold).selected : Set ι) := by sorry
