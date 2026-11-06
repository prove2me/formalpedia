-- Prove2me | Theorems.Thm_QEC_Locality_gridInterior_edge_vertex_pairwise_disjoint
-- name    : QEC.Locality.gridInterior_edge_vertex_pairwise_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:46:28.265662+00:00
-- url     : https://prove2.me/theorems/7294124e-0895-45f2-bb70-070093591878
-- title:
--   Locality: grid Interior edge vertex pairwise disjoint
-- statement:
--   The Locality construction uses the grid Interior edge vertex pairwise disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L2152-L2184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L2152-L2184

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
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
attribute [local instance] QEC.Locality.instClassicalDecidableRecursive

theorem QEC.Locality.gridInterior_edge_vertex_pairwise_disjoint
    (embedding : UnitSeparatedEmbedding2D ι) (w ell : ℝ)
    (t : GridTranslation w) :
    Disjoint (gridInteriorQubits embedding w ell t)
        (gridEdgeBufferQubits embedding w ell t) ∧
      Disjoint (gridInteriorQubits embedding w ell t)
        (gridVertexBufferQubits embedding w ell t) ∧
      Disjoint (gridEdgeBufferQubits embedding w ell t)
        (gridVertexBufferQubits embedding w ell t) := by sorry
