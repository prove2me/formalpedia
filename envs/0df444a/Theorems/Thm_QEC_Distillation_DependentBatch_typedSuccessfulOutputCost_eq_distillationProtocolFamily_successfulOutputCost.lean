-- Prove2me | Theorems.Thm_QEC_Distillation_DependentBatch_typedSuccessfulOutputCost_eq_distillationProtocolFamily_successfulOutputCost
-- name    : QEC.Distillation.DependentBatch.typedSuccessfulOutputCost_eq_distillationProtocolFamily_successfulOutputCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:01:27.112252+00:00
-- url     : https://prove2.me/theorems/a5ce05f4-4704-41df-8685-6f9e6bbbd640
-- title:
--   Dependent Batch: typed Successful Output Cost eq distillation Protocol Family successful Output Cost
-- statement:
--   A typed finite-slot cost agrees with the #458 family cost when its actual
--   input and output slot cardinalities and its yield factor have been separately
--   identified with that family index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/DependentBatch.lean#L147-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/DependentBatch.lean#L147-L166

import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Core_DependentBatch
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.DependentBatch
open Semantics
open scoped BigOperators
universe u v

theorem QEC.Distillation.DependentBatch.typedSuccessfulOutputCost_eq_distillationProtocolFamily_successfulOutputCost
    {Resource Input Output Index : Type u}
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource]
    [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
    [FiniteQuantumSystem Input]
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output]
    (family : DistillationProtocolFamily Resource Input Output Index) (index : Index)
    (InputSlots OutputSlots : Type*) [Fintype InputSlots] [Fintype OutputSlots]
    (yieldFactor : NNReal)
    (hinput : Fintype.card InputSlots = family.inputResourceCount index)
    (houtput : Fintype.card OutputSlots = family.outputResourceCount index)
    (hyield : (yieldFactor : ℝ) =
      (family.protocol index).run.successProbability) :
    typedSuccessfulOutputCost InputSlots OutputSlots yieldFactor =
      family.successfulOutputCost index := by sorry
