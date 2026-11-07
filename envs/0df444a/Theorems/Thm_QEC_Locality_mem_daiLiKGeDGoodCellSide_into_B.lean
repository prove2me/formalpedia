-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiKGeDGoodCellSide_into_B
-- name    : QEC.Locality.mem_daiLiKGeDGoodCellSide_into_B
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:17:23.45084+00:00
-- url     : https://prove2.me/theorems/0d8416f2-c876-4e12-8fde-23461b8ef21a
-- title:
--   Locality: mem dai Li KGe DGood Cell Side into B
-- statement:
--   Every source side strip of a good grid cell is one of the canonical grid
--   side components of the assembled `k >= d` region `B`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L4425-L4476
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L4425-L4476

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

theorem QEC.Locality.mem_daiLiKGeDGoodCellSide_into_B
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ) (hOccupied : cell ∈ embedding.gridOccupiedCells w (gridOrigin w t))
    (side : Fin 4) (q : ι)
    (hq : q ∈ daiLiRectangleSideStripQubits embedding ell
      (gridCellLower w (gridOrigin w t) cell) (gridCellUpper w (gridOrigin w t) cell) side)
    (hNotSeparator : q ∉ daiLiKGeDSeparator P embedding threshold w ell t cells rectangles) :
    q ∈ (daiLiKGeDBSubsystem P embedding d threshold w ell t cells rectangles).selected := by sorry
