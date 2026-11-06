-- Prove2me | Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
-- name    : QEC.Locality.mem_centeredRectangleQubits_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:49:04.550236+00:00
-- url     : https://prove2.me/theorems/4340d43c-7e8a-450d-8112-94896353daee
-- title:
--   Locality: mem centered Rectangle Qubits iff
-- statement:
--   The Locality construction uses the mem centered Rectangle Qubits iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L588-L592
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L588-L592

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

theorem QEC.Locality.mem_centeredRectangleQubits_iff (embedding : UnitSeparatedEmbedding2D ι)
    (center : ℝ × ℝ) (horizontalRadius verticalRadius : ℝ) (q : ι) :
    q ∈ centeredRectangleQubits embedding center horizontalRadius verticalRadius ↔
      embedding.point q ∈ centeredRectangle center horizontalRadius verticalRadius := by sorry
