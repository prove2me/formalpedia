-- Prove2me | Theorems.Thm_QEC_Locality_daiLiFiniteGridVertexBuffer_subset_gridVertexBuffer
-- name    : QEC.Locality.daiLiFiniteGridVertexBuffer_subset_gridVertexBuffer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:17:16.248685+00:00
-- url     : https://prove2.me/theorems/9db39c88-8e02-4606-a7d5-255f0b75392e
-- title:
--   Locality: dai Li Finite Grid Vertex Buffer subset grid Vertex Buffer
-- statement:
--   The full finite vertex buffer is counted by the selected periodic vertex
--   event.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1487-L1496
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1487-L1496

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

theorem QEC.Locality.daiLiFiniteGridVertexBuffer_subset_gridVertexBuffer
    (embedding : UnitSeparatedEmbedding2D ι) {w : ℝ} (hw : 0 < w)
    (ell : ℝ) (origin : ℝ × ℝ) (t : GridTranslation w)
    (ht : phase w origin = t) :
    daiLiFiniteGridVertexBuffer embedding w ell origin ⊆
      gridVertexBufferQubits embedding w ell t := by sorry
