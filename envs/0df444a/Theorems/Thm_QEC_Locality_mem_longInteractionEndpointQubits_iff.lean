-- Prove2me | Theorems.Thm_QEC_Locality_mem_longInteractionEndpointQubits_iff
-- name    : QEC.Locality.mem_longInteractionEndpointQubits_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:49:14.387313+00:00
-- url     : https://prove2.me/theorems/b8cf4c1f-d71c-45d3-a768-a0b55c0bdda4
-- title:
--   Locality: mem long Interaction Endpoint Qubits iff
-- statement:
--   The Locality construction uses the mem long Interaction Endpoint Qubits iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L2000-L2005
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L2000-L2005

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

theorem QEC.Locality.mem_longInteractionEndpointQubits_iff
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (q : ι) :
    q ∈ longInteractionEndpointQubits P embedding threshold ↔
      0 < P.daiLiInteractionCounter embedding threshold q := by sorry
