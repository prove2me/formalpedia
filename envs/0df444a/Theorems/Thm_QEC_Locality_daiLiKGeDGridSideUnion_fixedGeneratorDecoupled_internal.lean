-- Prove2me | Theorems.Thm_QEC_Locality_daiLiKGeDGridSideUnion_fixedGeneratorDecoupled_internal
-- name    : QEC.Locality.daiLiKGeDGridSideUnion_fixedGeneratorDecoupled_internal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:17:00.769862+00:00
-- url     : https://prove2.me/theorems/77fefa89-d1f0-45ec-8376-d526dc5b037d
-- title:
--   Locality: dai Li KGe DGrid Side Union fixed Generator Decoupled internal
-- statement:
--   The two finite `k >= d` side unions are fixed-generator decoupled.  This
--   is the cross-family Union-Lemma contract for `B`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3702-L3775
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3702-L3775

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

theorem QEC.Locality.daiLiKGeDGridSideUnion_fixedGeneratorDecoupled_internal
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEll : 0 < ell) (hWidth : 0 < w) (hThresholdEll : threshold ≤ ell) :
    P.fixedGeneratorDecoupled
      ((daiLiKGeDGridSideUnionSubsystem P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected : Set ι)
      ((daiLiKGeDInternalSideUnionSubsystem P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected : Set ι) := by sorry
