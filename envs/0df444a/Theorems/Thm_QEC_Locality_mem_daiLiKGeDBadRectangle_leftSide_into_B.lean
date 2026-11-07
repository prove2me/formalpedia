-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiKGeDBadRectangle_leftSide_into_B
-- name    : QEC.Locality.mem_daiLiKGeDBadRectangle_leftSide_into_B
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:17:22.367631+00:00
-- url     : https://prove2.me/theorems/fc622003-3275-403a-abd3-1bd3fae1aa54
-- title:
--   Locality: mem dai Li KGe DBad Rectangle left Side into B
-- statement:
--   The left edge strip of an actual bad-cell rectangle is contained in the
--   canonical left grid-side component.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L4033-L4115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L4033-L4115

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

theorem QEC.Locality.mem_daiLiKGeDBadRectangle_leftSide_into_B
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEll : 0 < ell) (cell : ℤ × ℤ)
    (hCell : cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t))
    (slot : ℕ) (hSlot : slot < (rectangles cell).length) (q : ι)
    (hq : q ∈ daiLiRectangleSideStripQubits embedding ell
      ((rectangles cell).get ⟨slot, hSlot⟩).1 ((rectangles cell).get ⟨slot, hSlot⟩).2 0)
    (hNotSeparator : q ∉ daiLiKGeDSeparator P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles) :
    q ∈ (daiLiKGeDBSubsystem P embedding d threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected := by sorry
