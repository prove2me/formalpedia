-- Prove2me | Theorems.Thm_QEC_Locality_card_daiLiRectangleSideStrip_lt_distance_of_box_scale
-- name    : QEC.Locality.card_daiLiRectangleSideStrip_lt_distance_of_box_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:15:55.526506+00:00
-- url     : https://prove2.me/theorems/655e0716-5753-4d9f-8d2a-f049ebf8e8f6
-- title:
--   Locality: card dai Li Rectangle Side Strip lt distance of box scale
-- statement:
--   Under the Dai--Li box scale, every one of the four finite edge strips of
--   a subdivision rectangle has cardinality strictly below the distance.  This is
--   the local `B` recovery budget; it is proved from packing rather than supplied
--   as a per-strip cardinality witness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2181-L2225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2181-L2225

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

theorem QEC.Locality.card_daiLiRectangleSideStrip_lt_distance_of_box_scale
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (ell w : ℝ)
    (lower upper : ℝ × ℝ) (hEll : 1 ≤ ell) (hCellWidth : 5 * ell ≤ w)
    (hSpan : upper.1 - lower.1 = w)
    (hMinimumHeight : 5 * ell ≤ upper.2 - lower.2)
    (hMaximumHeight : upper.2 - lower.2 ≤ w)
    (hSideScale : 12 * ell * w < d) (side : Fin 4) :
    ((daiLiRectangleSideStripQubits embedding ell lower upper side).card : ℝ) < d := by sorry
