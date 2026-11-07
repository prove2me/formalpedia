-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_quantumChannel_apply_input_of_explicit_support
-- name    : QEC.Distillation.HH18Parameterized.quantumChannel_apply_input_of_explicit_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:05:08.762863+00:00
-- url     : https://prove2.me/theorems/d00cc8a5-dda7-4d81-b277-7bba7ad1342d
-- title:
--   HH18 Parameterized: quantum Channel apply input of explicit support
-- statement:
--   A quantum channel sends an explicitly supported finite mixture to the
--   corresponding mixture of its pointwise images.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceConsumerSupport.lean#L23-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceConsumerSupport.lean#L23-L38

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceConsumerSupport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Semantics
open scoped BigOperators
universe u

theorem QEC.Distillation.HH18Parameterized.quantumChannel_apply_input_of_explicit_support
    {ι H K : Type u} (support : Finset ι)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (channel : QuantumChannel H K) (input : Operator H) (weight : ι → Complex)
    (inputState : ι → DensityOperator H) (outputState : ι → DensityOperator K)
    (hinput : input = support.sum (fun i => weight i • (inputState i).toOperator))
    (hpointwise : ∀ i, channel (inputState i).toOperator = (outputState i).toOperator) :
    channel input = support.sum (fun i => weight i • (outputState i).toOperator) := by sorry
