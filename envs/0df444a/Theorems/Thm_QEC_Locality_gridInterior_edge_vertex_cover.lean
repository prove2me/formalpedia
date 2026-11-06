-- Prove2me | Theorems.Thm_QEC_Locality_gridInterior_edge_vertex_cover
-- name    : QEC.Locality.gridInterior_edge_vertex_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:47:05.593465+00:00
-- url     : https://prove2.me/theorems/64bd502c-f586-4b1b-a6d2-f723b6a15664
-- title:
--   Locality: grid Interior edge vertex cover
-- statement:
--   In the `d >= k` branch, where DL24 proves there are no bad rectangles,
--   the actual grid predicates form the source `A/B/C` partition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L2188-L2202
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L2188-L2202

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

theorem QEC.Locality.gridInterior_edge_vertex_cover
    (embedding : UnitSeparatedEmbedding2D ι) (w ell : ℝ)
    (t : GridTranslation w) :
    gridInteriorQubits embedding w ell t ∪
        gridEdgeBufferQubits embedding w ell t ∪
        gridVertexBufferQubits embedding w ell t = Finset.univ := by sorry
