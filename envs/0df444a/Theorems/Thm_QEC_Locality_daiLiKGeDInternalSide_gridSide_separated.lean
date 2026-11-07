-- Prove2me | Theorems.Thm_QEC_Locality_daiLiKGeDInternalSide_gridSide_separated
-- name    : QEC.Locality.daiLiKGeDInternalSide_gridSide_separated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:16:53.120205+00:00
-- url     : https://prove2.me/theorems/1d65e318-e8bc-47c9-8cc8-7881352c70d1
-- title:
--   Locality: dai Li KGe DInternal Side grid Side separated
-- statement:
--   A canonical internal bad-rectangle cut is separated from every finite
--   grid-side component.  The proof uses the explicit host-cell trimming instead
--   of an implicit periodic-space convention.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3552-L3614
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3552-L3614

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

theorem QEC.Locality.daiLiKGeDInternalSide_gridSide_separated
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
    (hEll : 0 < ell) (hWidth : 0 < w)
    (cell : ℤ × ℤ) (slot : ℕ)
    (hCandidate : (cell, slot) ∈ daiLiKGeDInternalSideCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (gridSide : DaiLiGridSideIndex) {p q : ι}
    (hp : p ∈ daiLiRectangleSideStripQubits embedding ell
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (cell, slot)).1
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (cell, slot)).2 3)
    (hq : q ∈ daiLiGridSideStripQubits embedding w ell (2 * ell) (gridOrigin w t) gridSide) :
    ell ≤ embedding.distance p q := by sorry
