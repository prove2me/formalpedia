-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolInstrument_bornWeight_tensorPowerProductInput
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolInstrument_bornWeight_tensorPowerProductInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:02:19.142475+00:00
-- url     : https://prove2.me/theorems/e95f4389-3ab2-4dc5-84c4-69683148a9fb
-- title:
--   HH18 Parameterized: decoded Retry Pool Instrument born Weight tensor Power Product Input
-- statement:
--   On actual tensorized measured-resource blocks, every pooled observed
--   history has the recursively factored observed Born mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Core.lean#L208-L221
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Core.lean#L208-L221

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Core
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedRetryPoolClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolInstrument_bornWeight_tensorPowerProductInput {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (attempts required : Nat)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace)
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0))
    (history : tensorPowerHistory DistillationOutcome attempts) :
    (decodedRetryPoolInstrument h hdegree attempts required).bornWeight
        ⟨history, PUnit.unit⟩
          (tensorPowerProductInput (prepareMeasuredResources m w inputs) rhoUnit attempts) =
      tensorPowerBornProduct (decodedInstrument h hdegree)
        (prepareMeasuredResources m w inputs) attempts history := by sorry
