-- Prove2me | Theorems.Thm_QEC_Locality_fixedGeneratorOuterBoundary_centeredRectangle_subset_generalGrowthBoundary
-- name    : QEC.Locality.fixedGeneratorOuterBoundary_centeredRectangle_subset_generalGrowthBoundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:04:27.992659+00:00
-- url     : https://prove2.me/theorems/0cd766b5-5884-464d-9a9b-683d667ce64f
-- title:
--   Locality: fixed Generator Outer Boundary centered Rectangle subset general Growth Boundary
-- statement:
--   The computed general boundary contains every fixed-generator outer
--   boundary qubit of the previous rectangle.  Short crossings are caught by the
--   explicit collar; only genuinely long crossings use the interaction counter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1184-L1224
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1184-L1224

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

theorem QEC.Locality.fixedGeneratorOuterBoundary_centeredRectangle_subset_generalGrowthBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold : ℝ)
    (hHorizontal : innerHorizontalRadius ≤ outerHorizontalRadius)
    (hVertical : innerVerticalRadius ≤ outerVerticalRadius) :
    P.fixedGeneratorOuterBoundary
        ((centeredRectangleSubsystem embedding center innerHorizontalRadius
          innerVerticalRadius).selected : Set ι) ⊆
      ((centeredRectangleGeneralGrowthBoundary P embedding center
        innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
        outerVerticalRadius threshold).selected : Set ι) := by sorry
