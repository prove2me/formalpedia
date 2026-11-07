-- Prove2me | Theorems.Thm_QEC_Locality_card_daiLiVertexNeighborhoodQubits_le
-- name    : QEC.Locality.card_daiLiVertexNeighborhoodQubits_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:12:47.620237+00:00
-- url     : https://prove2.me/theorems/235271e7-682b-4ed2-9412-8e227f79273c
-- title:
--   Locality: card dai Li Vertex Neighborhood Qubits le
-- statement:
--   Packing controls each actual `2 * ell` vertex neighborhood by the
--   source's `96 * ell^2` local term.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1171-L1183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1171-L1183

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

theorem QEC.Locality.card_daiLiVertexNeighborhoodQubits_le
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (hEll : 1 ≤ ell)
    (vertex : ℝ × ℝ) :
    ((daiLiVertexNeighborhoodQubits embedding ell vertex).card : ℝ) ≤
      96 * ell ^ 2 := by sorry
