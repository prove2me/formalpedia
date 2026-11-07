-- Prove2me | Theorems.Thm_QEC_Locality_exists_daiLiBadGridCellSubdivision
-- name    : QEC.Locality.exists_daiLiBadGridCellSubdivision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:11:44.37567+00:00
-- url     : https://prove2.me/theorems/e3139e9d-87fb-4695-8816-d148c83b4ff0
-- title:
--   Locality: exists dai Li Bad Grid Cell Subdivision
-- statement:
--   Every finite bad grid-cell family has the project-owned corrected
--   support-free subdivision.  The returned rectangle family is constructed by
--   #496; its factor-30 count is deliberately not attributed to DL24.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L333-L380
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L333-L380

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

theorem QEC.Locality.exists_daiLiBadGridCellSubdivision
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold ell : ℝ) (d : Nat)
    (w : ℝ) (origin : ℝ × ℝ) (hEll : 0 < ell) (hHeight : 5 * ell ≤ w) :
    ∃ (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
      (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))),
      (∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
        DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
          ((daiLiGridCellCenter w origin cell).2 - w / 2)
          ((daiLiGridCellCenter w origin cell).2 + w / 2) (atoms cell)) ∧
      (∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
        rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
          ((daiLiGridCellCenter w origin cell).1 - w / 2)
          ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell)) ∧
      (∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
        (rectangles cell).IsChain (fun first second => first.2.2 = second.1.2)) ∧
      (∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
        DaiLiPairwiseDisjointQubitRectangles embedding (rectangles cell)) ∧
      (∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
        daiLiRectangleQubitsCover embedding (rectangles cell) =
          daiLiGridCellClosedQubits embedding w origin cell) ∧
      (∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
        ∀ rectangle ∈ rectangles cell,
          5 * ell ≤ rectangle.2.2 - rectangle.1.2 ∧
            (10 * regionInteractionCounter P embedding threshold
                (embedding.qubitsInRectangle rectangle.1 rectangle.2) ≤ d ∨
              rectangle.2.2 - rectangle.1.2 ≤ 10 * ell)) ∧
      (∑ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
        (rectangles cell).length) * d ≤
          30 * daiLiBadGridTotalF P embedding threshold d w origin := by sorry
