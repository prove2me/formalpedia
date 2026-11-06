-- Prove2me | Theorems.Thm_QEC_Locality_mem_squareQubits_iff
-- name    : QEC.Locality.mem_squareQubits_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:49:03.978399+00:00
-- url     : https://prove2.me/theorems/3de86499-7f11-4120-8616-a3a0dffd4d46
-- title:
--   Locality: mem square Qubits iff
-- statement:
--   The Locality construction uses the mem square Qubits iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L77-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L77-L81

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

theorem QEC.Locality.mem_squareQubits_iff (embedding : UnitSeparatedEmbedding2D ι)
    (center : ℝ × ℝ) (radius : ℝ) (q : ι) :
    q ∈ squareQubits embedding center radius ↔
      embedding.point q ∈ centeredSquare center radius := by sorry
