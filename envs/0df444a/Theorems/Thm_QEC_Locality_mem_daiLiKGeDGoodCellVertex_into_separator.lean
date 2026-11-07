-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiKGeDGoodCellVertex_into_separator
-- name    : QEC.Locality.mem_daiLiKGeDGoodCellVertex_into_separator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:17:47.358524+00:00
-- url     : https://prove2.me/theorems/9d45f834-16fe-40ab-8b25-f790a997da80
-- title:
--   Locality: mem dai Li KGe DGood Cell Vertex into separator
-- statement:
--   A vertex neighborhood of a good grid cell belongs to the periodic vertex
--   component of the concrete `k >= d` separator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L4554-L4582
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L4554-L4582

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

theorem QEC.Locality.mem_daiLiKGeDGoodCellVertex_into_separator
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) {w : ℝ} (hw : 0 < w)
    (threshold ell : ℝ) (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ) (vertex : Fin 4) (q : ι)
    (hq : q ∈ daiLiVertexNeighborhoodQubits embedding ell
      (daiLiRectangleVertex
        (gridCellLower w (gridOrigin w t) cell, gridCellUpper w (gridOrigin w t) cell) vertex)) :
    q ∈ daiLiKGeDSeparator P embedding threshold w ell t cells rectangles := by sorry
