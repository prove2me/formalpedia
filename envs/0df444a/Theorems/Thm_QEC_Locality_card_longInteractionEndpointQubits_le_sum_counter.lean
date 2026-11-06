-- Prove2me | Theorems.Thm_QEC_Locality_card_longInteractionEndpointQubits_le_sum_counter
-- name    : QEC.Locality.card_longInteractionEndpointQubits_le_sum_counter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:45:16.469201+00:00
-- url     : https://prove2.me/theorems/1b917f95-e623-4238-b9c8-22c24c8818a8
-- title:
--   Locality: card long Interaction Endpoint Qubits le sum counter
-- statement:
--   Every bad qubit contributes at least one incidence to the global counter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1974-L1997
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1974-L1997

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

theorem QEC.Locality.card_longInteractionEndpointQubits_le_sum_counter
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) :
    (longInteractionEndpointQubits P embedding threshold).card ≤
      ∑ q, P.daiLiInteractionCounter embedding threshold q := by sorry
