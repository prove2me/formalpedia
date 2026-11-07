-- Prove2me | Theorems.Thm_QEC_Locality_daiLiKGeDInternalSides_sameHost_separated
-- name    : QEC.Locality.daiLiKGeDInternalSides_sameHost_separated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:16:29.571743+00:00
-- url     : https://prove2.me/theorems/88244fc1-e9fb-4c06-94e5-77cbc81dcd65
-- title:
--   Locality: dai Li KGe DInternal Sides same Host separated
-- statement:
--   Two distinct internal cuts in one actual bad-rectangle list are separated
--   by at least `ell`.  This is the list-order branch of the finite `B` geometry.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3229-L3329
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3229-L3329

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

theorem QEC.Locality.daiLiKGeDInternalSides_sameHost_separated
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
    (hEll : 0 < ell) (cell : ℤ × ℤ) (slot otherSlot : ℕ)
    (hCandidate : (cell, slot) ∈ daiLiKGeDInternalSideCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (hOtherCandidate : (cell, otherSlot) ∈ daiLiKGeDInternalSideCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (hne : slot ≠ otherSlot) {p q : ι}
    (hp : p ∈ daiLiRectangleSideStripQubits embedding ell
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (cell, slot)).1
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (cell, slot)).2 3)
    (hq : q ∈ daiLiRectangleSideStripQubits embedding ell
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (cell, otherSlot)).1
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (cell, otherSlot)).2 3) :
    ell ≤ embedding.distance p q := by sorry
