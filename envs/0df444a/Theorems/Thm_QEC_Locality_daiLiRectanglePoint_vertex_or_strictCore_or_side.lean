-- Prove2me | Theorems.Thm_QEC_Locality_daiLiRectanglePoint_vertex_or_strictCore_or_side
-- name    : QEC.Locality.daiLiRectanglePoint_vertex_or_strictCore_or_side
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:12:41.129113+00:00
-- url     : https://prove2.me/theorems/9e43e17a-b80a-400d-9901-eddc4214ca11
-- title:
--   Locality: dai Li Rectangle Point vertex or strict Core or side
-- statement:
--   A point of one actual rectangle which avoids all four `2 * ell` vertex
--   neighborhoods lies either in its strict core or in one of the four concrete
--   source side strips.  This is the local geometric assignment used for the
--   finite `k >= d` partition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1022-L1137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1022-L1137

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

theorem QEC.Locality.daiLiRectanglePoint_vertex_or_strictCore_or_side
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (hEll : 0 < ell)
    (lower upper : ℝ × ℝ) (q : ι)
    (hq : q ∈ embedding.qubitsInRectangle lower upper) :
    (∃ vertex : Fin 4,
      q ∈ daiLiVertexNeighborhoodQubits embedding ell
        (daiLiRectangleVertex (lower, upper) vertex)) ∨
      (lower.1 + ell < (embedding.point q).1 ∧
        (embedding.point q).1 < upper.1 - ell ∧
          lower.2 + ell < (embedding.point q).2 ∧
            (embedding.point q).2 < upper.2 - ell) ∨
      ∃ side : Fin 4,
        q ∈ daiLiRectangleSideStripQubits embedding ell lower upper side := by sorry
