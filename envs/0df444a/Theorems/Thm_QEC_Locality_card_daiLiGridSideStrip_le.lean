-- Prove2me | Theorems.Thm_QEC_Locality_card_daiLiGridSideStrip_le
-- name    : QEC.Locality.card_daiLiGridSideStrip_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:15:04.39522+00:00
-- url     : https://prove2.me/theorems/e4a7aae7-6602-46e7-b2b8-57c4b9ee318b
-- title:
--   Locality: card dai Li Grid Side Strip le
-- statement:
--   Every concrete vertical or horizontal grid-side strip has the expected
--   area packing estimate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1506-L1534
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1506-L1534

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

theorem QEC.Locality.card_daiLiGridSideStrip_le
    (embedding : UnitSeparatedEmbedding2D ι) (w edgeRadius vertexRadius : ℝ)
    (origin : ℝ × ℝ) (side : DaiLiGridSideIndex)
    (hEdge : 1 ≤ 2 * edgeRadius) (hLong : 1 ≤ w - 2 * vertexRadius) :
    ((daiLiGridSideStripQubits embedding w edgeRadius vertexRadius origin side).card : ℝ) ≤
      12 * edgeRadius * (w - 2 * vertexRadius) := by sorry
