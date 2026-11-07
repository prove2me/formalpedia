-- Prove2me | Theorems.Thm_QEC_Locality_daiLiBadGridRectangle_horizontalSpan
-- name    : QEC.Locality.daiLiBadGridRectangle_horizontalSpan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:10:06.69428+00:00
-- url     : https://prove2.me/theorems/d87cf87f-fc53-4b56-b3fe-8e1fe8693942
-- title:
--   Locality: dai Li Bad Grid Rectangle horizontal Span
-- statement:
--   Every #496 rectangle for a bad grid cell retains the exact horizontal
--   span of its parent grid square.  This is the width fact used by both the
--   short-rectangle packing recovery and its finite side-strip estimates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L385-L400
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L385-L400

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

theorem QEC.Locality.daiLiBadGridRectangle_horizontalSpan
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (w : ℝ) (origin : ℝ × ℝ) (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w origin cell).1 - w / 2)
        ((daiLiGridCellCenter w origin cell).1 + w / 2) d
        (atoms cell))
    (cell : ℤ × ℤ) (hcell : cell ∈ daiLiBadGridCells P embedding threshold d w origin)
    (rectangle : (ℝ × ℝ) × (ℝ × ℝ)) (hrectangle : rectangle ∈ rectangles cell) :
    rectangle.2.1 - rectangle.1.1 = w := by sorry
