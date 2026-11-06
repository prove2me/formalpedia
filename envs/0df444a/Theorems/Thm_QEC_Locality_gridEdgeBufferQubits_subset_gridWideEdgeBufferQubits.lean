-- Prove2me | Theorems.Thm_QEC_Locality_gridEdgeBufferQubits_subset_gridWideEdgeBufferQubits
-- name    : QEC.Locality.gridEdgeBufferQubits_subset_gridWideEdgeBufferQubits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:46:13.577369+00:00
-- url     : https://prove2.me/theorems/885dba6b-bcae-473b-90ca-7d2093c5eae2
-- title:
--   Locality: grid Edge Buffer Qubits subset grid Wide Edge Buffer Qubits
-- statement:
--   The Locality construction uses the grid Edge Buffer Qubits subset grid Wide Edge Buffer Qubits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L2138-L2150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L2138-L2150

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

theorem QEC.Locality.gridEdgeBufferQubits_subset_gridWideEdgeBufferQubits
    (embedding : UnitSeparatedEmbedding2D ι) (w ell : ℝ)
    (t : GridTranslation w) (hell : 0 ≤ ell) :
    gridEdgeBufferQubits embedding w ell t ⊆
      gridWideEdgeBufferQubits embedding w ell t := by sorry
