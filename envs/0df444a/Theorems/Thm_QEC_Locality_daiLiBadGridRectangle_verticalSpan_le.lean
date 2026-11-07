-- Prove2me | Theorems.Thm_QEC_Locality_daiLiBadGridRectangle_verticalSpan_le
-- name    : QEC.Locality.daiLiBadGridRectangle_verticalSpan_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:10:28.797743+00:00
-- url     : https://prove2.me/theorems/6b671235-344a-4a0f-9168-c4f990cecf1e
-- title:
--   Locality: dai Li Bad Grid Rectangle vertical Span le
-- statement:
--   Every actual greedy rectangle remains vertically inside its parent grid
--   cell.  This is the finite atom-chain fact needed to use one box-scale growth
--   and strip budget for all bad rectangles.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L470-L498
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L470-L498

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

theorem QEC.Locality.daiLiBadGridRectangle_verticalSpan_le
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
    (hEll : 0 < ell) (cell : ℤ × ℤ)
    (hcell : cell ∈ daiLiBadGridCells P embedding threshold d w origin)
    (rectangle : (ℝ × ℝ) × (ℝ × ℝ)) (hrectangle : rectangle ∈ rectangles cell) :
    rectangle.2.2 - rectangle.1.2 ≤ w := by sorry
