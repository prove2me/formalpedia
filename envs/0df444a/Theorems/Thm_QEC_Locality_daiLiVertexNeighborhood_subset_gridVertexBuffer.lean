-- Prove2me | Theorems.Thm_QEC_Locality_daiLiVertexNeighborhood_subset_gridVertexBuffer
-- name    : QEC.Locality.daiLiVertexNeighborhood_subset_gridVertexBuffer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:10:46.222041+00:00
-- url     : https://prove2.me/theorems/5b200d08-a5ba-46d9-abcf-3a4ff9b1a88a
-- title:
--   Locality: dai Li Vertex Neighborhood subset grid Vertex Buffer
-- statement:
--   A finite Euclidean vertex neighborhood is contained in the periodic
--   vertex event for the same translated grid.  Thus the actual partition can use
--   the #385 averaged count without quotient-space boundary assumptions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1432-L1483
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1432-L1483

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

theorem QEC.Locality.daiLiVertexNeighborhood_subset_gridVertexBuffer
    (embedding : UnitSeparatedEmbedding2D ι) {w : ℝ} (hw : 0 < w)
    (ell : ℝ) (origin : ℝ × ℝ) (t : GridTranslation w)
    (ht : phase w origin = t) (vertex : ℤ × ℤ) :
    daiLiVertexNeighborhoodQubits embedding ell
      (origin.1 + (vertex.1 : ℝ) * w, origin.2 + (vertex.2 : ℝ) * w) ⊆
      gridVertexBufferQubits embedding w ell t := by sorry
