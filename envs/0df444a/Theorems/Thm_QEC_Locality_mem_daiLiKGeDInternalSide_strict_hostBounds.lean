-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiKGeDInternalSide_strict_hostBounds
-- name    : QEC.Locality.mem_daiLiKGeDInternalSide_strict_hostBounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:10:38.739183+00:00
-- url     : https://prove2.me/theorems/74c2f53c-adbc-4a07-86cb-097b94b2a344
-- title:
--   Locality: mem dai Li KGe DInternal Side strict host Bounds
-- statement:
--   Every canonical internal cut lies in the `4 * ell`-trimmed host cell.
--   The upper trimming uses the actual next list element, so it holds even when
--   the rectangle list has an arbitrary finite length.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3146-L3225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3146-L3225

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

theorem QEC.Locality.mem_daiLiKGeDInternalSide_strict_hostBounds
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
    (hEll : 0 < ell) (cell : ℤ × ℤ) (slot : ℕ)
    (hCandidate : (cell, slot) ∈ daiLiKGeDInternalSideCandidates P embedding threshold d
      w (gridOrigin w t) rectangles) (p : ι)
    (hp : p ∈ daiLiRectangleSideStripQubits embedding ell
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (cell, slot)).1
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (cell, slot)).2 3) :
    (gridOrigin w t).1 + (cell.1 : ℝ) * w + 2 * ell ≤ (embedding.point p).1 ∧
      (embedding.point p).1 ≤ (gridOrigin w t).1 + ((cell.1 : ℝ) + 1) * w - 2 * ell ∧
      (gridOrigin w t).2 + (cell.2 : ℝ) * w + 4 * ell ≤ (embedding.point p).2 ∧
      (embedding.point p).2 ≤ (gridOrigin w t).2 + ((cell.2 : ℝ) + 1) * w - 4 * ell := by sorry
