-- Prove2me | Theorems.Thm_QEC_Locality_daiLiBadGridRectangle_get_verticalOrder
-- name    : QEC.Locality.daiLiBadGridRectangle_get_verticalOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:09:42.515233+00:00
-- url     : https://prove2.me/theorems/b0d3cc68-5b42-4552-a954-05acdd540c14
-- title:
--   Locality: dai Li Bad Grid Rectangle get vertical Order
-- statement:
--   Earlier and later concrete #496 rectangle entries have vertically ordered
--   endpoints.  The statement uses natural list positions so it can be applied
--   directly to the finite `k >= d` region index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L587-L624
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L587-L624

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

theorem QEC.Locality.daiLiBadGridRectangle_get_verticalOrder
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
    (first second : ℕ) (hFirst : first < (rectangles cell).length)
    (hSecond : second < (rectangles cell).length) (hOrder : first < second) :
    ((rectangles cell).get ⟨first, hFirst⟩).2.2 ≤
      ((rectangles cell).get ⟨second, hSecond⟩).1.2 := by sorry
