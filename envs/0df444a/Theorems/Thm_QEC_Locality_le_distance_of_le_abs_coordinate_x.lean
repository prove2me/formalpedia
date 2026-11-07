-- Prove2me | Theorems.Thm_QEC_Locality_le_distance_of_le_abs_coordinate_x
-- name    : QEC.Locality.le_distance_of_le_abs_coordinate_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:09:50.645407+00:00
-- url     : https://prove2.me/theorems/e15c3c13-b8ef-47e2-8d0c-357626306608
-- title:
--   Locality: le distance of le abs coordinate x
-- statement:
--   A coordinate lower bound gives the corresponding Euclidean lower bound
--   for the concrete embedding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1611-L1620
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1611-L1620

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

theorem QEC.Locality.le_distance_of_le_abs_coordinate_x
    (embedding : UnitSeparatedEmbedding2D ι) {p q : ι} {r : ℝ}
    (h : r ≤ |(embedding.point p).1 - (embedding.point q).1|) :
    r ≤ embedding.distance p q := by sorry
