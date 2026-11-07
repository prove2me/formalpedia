-- Prove2me | Theorems.Thm_QEC_Locality_daiLiBadGridRectangle_adjacent_verticalBoundary
-- name    : QEC.Locality.daiLiBadGridRectangle_adjacent_verticalBoundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:12:29.773111+00:00
-- url     : https://prove2.me/theorems/01069f90-adf9-4c06-8b20-706006112ff4
-- title:
--   Locality: dai Li Bad Grid Rectangle adjacent vertical Boundary
-- statement:
--   Consecutive actual bad-rectangle entries meet exactly at their shared
--   horizontal cut.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L897-L921
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L897-L921

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

theorem QEC.Locality.daiLiBadGridRectangle_adjacent_verticalBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (w ell : ℝ) (origin : ℝ × ℝ) (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w origin cell).2 - w / 2)
        ((daiLiGridCellCenter w origin cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w origin cell).1 - w / 2)
        ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell))
    (cell : ℤ × ℤ) (hCell : cell ∈ daiLiBadGridCells P embedding threshold d w origin)
    (slot : ℕ) (hSlot : slot < (rectangles cell).length)
    (hNext : slot + 1 < (rectangles cell).length) :
    ((rectangles cell).get ⟨slot, hSlot⟩).2.2 =
      ((rectangles cell).get ⟨slot + 1, hNext⟩).1.2 := by sorry
