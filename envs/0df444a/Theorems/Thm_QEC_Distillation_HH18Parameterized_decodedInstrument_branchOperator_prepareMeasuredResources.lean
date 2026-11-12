-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedInstrument_branchOperator_prepareMeasuredResources
-- name    : QEC.Distillation.HH18Parameterized.decodedInstrument_branchOperator_prepareMeasuredResources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:38:17.499203+00:00
-- url     : https://prove2.me/theorems/70a438ea-6def-4f46-bdf6-4f7b3c046769
-- title:
--   HH18 Parameterized: decoded Instrument branch Operator prepare Measured Resources
-- statement:
--   On an actual measured resource family, a decoded coarse branch is its
--   literal Born weight times the normalized/completed decoded conditional
--   output.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrumentConditional.lean#L61-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrumentConditional.lean#L61-L84

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_NormalizedRun
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrumentConditional
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedInstrument_branchOperator_prepareMeasuredResources
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace)
    (outcome : DistillationOutcome) :
    (decodedInstrument h hdegree).branchOperator outcome
        (prepareMeasuredResources m w inputs).toOperator =
      (endpointWeight h hdegree inputs outcome : Complex) •
        ((resourceDecodedRun h hdegree inputs).conditionalOutput outcome).toOperator := by sorry
