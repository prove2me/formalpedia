-- Prove2me | Theorems.Thm_QEC_Locality_exists_daiLiBadGridRectangle_covering_qubit
-- name    : QEC.Locality.exists_daiLiBadGridRectangle_covering_qubit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:17:31.092996+00:00
-- url     : https://prove2.me/theorems/e22fe0be-cdd9-4b6d-b1db-a6b7a9c913d0
-- title:
--   Locality: exists dai Li Bad Grid Rectangle covering qubit
-- statement:
--   The #496 rectangle list of a bad grid cell gives every owned qubit a
--   concrete, in-range actual rectangle witness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L4480-L4520
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L4480-L4520

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

theorem QEC.Locality.exists_daiLiBadGridRectangle_covering_qubit
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
    (hw : 0 < w) (hEll : 0 < ell) (cell : ℤ × ℤ)
    (hCell : cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t))
    (q : ι) (hq : q ∈ embedding.gridCellQubits w (gridOrigin w t) cell) :
    ∃ slot : Fin (rectangles cell).length,
      q ∈ embedding.qubitsInRectangle ((rectangles cell).get slot).1
        ((rectangles cell).get slot).2 := by sorry
