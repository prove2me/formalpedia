-- Prove2me | Theorems.Thm_QEC_Locality_le_distance_of_le_abs_coordinate_y
-- name    : QEC.Locality.le_distance_of_le_abs_coordinate_y
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:08:58.314142+00:00
-- url     : https://prove2.me/theorems/24c91791-00cf-499b-8189-c316a43126db
-- title:
--   Locality: le distance of le abs coordinate y
-- statement:
--   The Locality construction uses the le distance of le abs coordinate y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1622-L1631
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1622-L1631

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

theorem QEC.Locality.le_distance_of_le_abs_coordinate_y
    (embedding : UnitSeparatedEmbedding2D ι) {p q : ι} {r : ℝ}
    (h : r ≤ |(embedding.point p).2 - (embedding.point q).2|) :
    r ≤ embedding.distance p q := by sorry
