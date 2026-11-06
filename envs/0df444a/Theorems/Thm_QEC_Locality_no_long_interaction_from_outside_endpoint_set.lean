-- Prove2me | Theorems.Thm_QEC_Locality_no_long_interaction_from_outside_endpoint_set
-- name    : QEC.Locality.no_long_interaction_from_outside_endpoint_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:05:02.226311+00:00
-- url     : https://prove2.me/theorems/ae1f8c59-28e4-417b-8594-f82881bb98e2
-- title:
--   Locality: no long interaction from outside endpoint set
-- statement:
--   The `k >= d` branch's disposal of every bad qubit removes every threshold-long
--   fixed-generator interaction from the remaining qubits.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L2009-L2020
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L2009-L2020

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

theorem QEC.Locality.no_long_interaction_from_outside_endpoint_set
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (p q : ι)
    (hp : p ∉ longInteractionEndpointQubits P embedding threshold) :
    ¬ (P.fixedGeneratorInteraction p q ∧ threshold ≤ embedding.distance p q) := by sorry
