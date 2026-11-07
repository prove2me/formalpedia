-- Prove2me | Theorems.Thm_QEC_Locality_daiLiKGeD_partition_pairwise
-- name    : QEC.Locality.daiLiKGeD_partition_pairwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:16:57.155621+00:00
-- url     : https://prove2.me/theorems/37f2aede-3d01-4826-b126-d0d0b9b222b8
-- title:
--   Locality: dai Li KGe D partition pairwise
-- statement:
--   The finite `k >= d` partition components are pairwise disjoint by the
--   chosen trimming and residual construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3877-L3898
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3877-L3898

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
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
attribute [local instance] QEC.Locality.instClassicalDecidableCorrectable

theorem QEC.Locality.daiLiKGeD_partition_pairwise
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    Disjoint (daiLiKGeDASubsystem P embedding d threshold w ell t cells rectangles).selected
      (daiLiKGeDTrimmedBSubsystem P embedding d threshold w ell t cells rectangles).selected ∧
    Disjoint (daiLiKGeDASubsystem P embedding d threshold w ell t cells rectangles).selected
      (daiLiKGeDResidualSubsystem P embedding d threshold w ell t cells rectangles).selected ∧
    Disjoint (daiLiKGeDTrimmedBSubsystem P embedding d threshold w ell t cells rectangles).selected
      (daiLiKGeDResidualSubsystem P embedding d threshold w ell t cells rectangles).selected := by sorry
