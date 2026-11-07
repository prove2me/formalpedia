-- Prove2me | Theorems.Thm_QEC_Locality_daiLiVertexNeighborhoodQubits_subset_badGridRectangleVertexBuffer
-- name    : QEC.Locality.daiLiVertexNeighborhoodQubits_subset_badGridRectangleVertexBuffer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:10:20.929235+00:00
-- url     : https://prove2.me/theorems/8f9df3ae-fc14-4477-8c6a-4e8ace5e1316
-- title:
--   Locality: dai Li Vertex Neighborhood Qubits subset bad Grid Rectangle Vertex Buffer
-- statement:
--   Every vertex neighborhood of an actual indexed bad-grid rectangle occurs
--   in the concrete finite rectangle-vertex component of the source separator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L979-L992
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L979-L992

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

theorem QEC.Locality.daiLiVertexNeighborhoodQubits_subset_badGridRectangleVertexBuffer
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ)
    (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ) (hCell : cell ∈ cells) (slot : ℕ)
    (hSlot : slot < (rectangles cell).length) (vertex : Fin 4) :
    daiLiVertexNeighborhoodQubits embedding ell
        (daiLiRectangleVertex ((rectangles cell).get ⟨slot, hSlot⟩) vertex) ⊆
      daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles := by sorry
