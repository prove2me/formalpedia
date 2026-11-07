-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiBadGridCells_iff
-- name    : QEC.Locality.mem_daiLiBadGridCells_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:08:58.760875+00:00
-- url     : https://prove2.me/theorems/02ca2555-6fbf-4e90-a44f-b8a31271934b
-- title:
--   Locality: mem dai Li Bad Grid Cells iff
-- statement:
--   The Locality construction uses the mem dai Li Bad Grid Cells iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L233-L241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L233-L241

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

theorem QEC.Locality.mem_daiLiBadGridCells_iff
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (w : ℝ) (origin : ℝ × ℝ) (cell : ℤ × ℤ) :
    cell ∈ daiLiBadGridCells P embedding threshold d w origin ↔
      cell ∈ embedding.gridOccupiedCells w origin ∧
        IsBadInteractionSquare P embedding threshold d
          (daiLiGridCellCenter w origin cell) (w / 2) := by sorry
