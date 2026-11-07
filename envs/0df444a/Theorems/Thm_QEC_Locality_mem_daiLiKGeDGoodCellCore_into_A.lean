-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiKGeDGoodCellCore_into_A
-- name    : QEC.Locality.mem_daiLiKGeDGoodCellCore_into_A
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:17:55.297997+00:00
-- url     : https://prove2.me/theorems/ce22b087-234b-4684-ac8e-f71f69011e35
-- title:
--   Locality: mem dai Li KGe DGood Cell Core into A
-- statement:
--   A strict, separator-free point of a good grid cell is selected by the
--   actual good-cell member of the finite `A` family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L4524-L4550
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L4524-L4550

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

theorem QEC.Locality.mem_daiLiKGeDGoodCellCore_into_A
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ)
    (hCandidate : Sum.inl cell ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles) (q : ι)
    (hRect : q ∈ embedding.qubitsInRectangle
      (gridCellLower w (gridOrigin w t) cell) (gridCellUpper w (gridOrigin w t) cell))
    (hNotSeparator : q ∉ daiLiKGeDSeparator P embedding threshold w ell t cells rectangles)
    (hStrict : (gridCellLower w (gridOrigin w t) cell).1 + ell < (embedding.point q).1 ∧
      (embedding.point q).1 < (gridCellUpper w (gridOrigin w t) cell).1 - ell ∧
        (gridCellLower w (gridOrigin w t) cell).2 + ell < (embedding.point q).2 ∧
          (embedding.point q).2 < (gridCellUpper w (gridOrigin w t) cell).2 - ell) :
    q ∈ (daiLiKGeDASubsystem P embedding d threshold w ell t cells rectangles).selected := by sorry
