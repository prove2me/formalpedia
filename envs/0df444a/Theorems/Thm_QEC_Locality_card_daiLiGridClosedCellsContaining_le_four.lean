-- Prove2me | Theorems.Thm_QEC_Locality_card_daiLiGridClosedCellsContaining_le_four
-- name    : QEC.Locality.card_daiLiGridClosedCellsContaining_le_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:11:25.17455+00:00
-- url     : https://prove2.me/theorems/ac6f183c-7f40-4154-acb0-c00d55b4c501
-- title:
--   Locality: card dai Li Grid Closed Cells Containing le four
-- statement:
--   Closed witness squares overlap at most four times.  This is the explicit
--   boundary charge replacing the paper's informal generic perturbation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L160-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L160-L220

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

theorem QEC.Locality.card_daiLiGridClosedCellsContaining_le_four
    (embedding : UnitSeparatedEmbedding2D ι) {w : ℝ} (hw : 0 < w)
    (origin : ℝ × ℝ) (q : ι) :
    (daiLiGridClosedCellsContaining embedding w origin q).card ≤ 4 := by sorry
