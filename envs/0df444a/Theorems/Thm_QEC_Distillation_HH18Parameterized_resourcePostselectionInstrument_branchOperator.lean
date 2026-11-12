-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_resourcePostselectionInstrument_branchOperator
-- name    : QEC.Distillation.HH18Parameterized.resourcePostselectionInstrument_branchOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:00:22.569492+00:00
-- url     : https://prove2.me/theorems/ff2103c8-4d6e-43eb-bf8c-00f06ed2d218
-- title:
--   HH18 Parameterized: resource Postselection Instrument branch Operator
-- statement:
--   Before total decoding, the retained visible branch is exactly the real
--   postselection branch after actual resource consumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrument.lean#L131-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrument.lean#L131-L152

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Decoder
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedInstrumentClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.resourcePostselectionInstrument_branchOperator {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (outcome : DistillationOutcome) (A : Operator (PhysicalRegister m w)) :
    (resourcePostselectionInstrument h hdegree).branchOperator
        ⟨PUnit.unit, outcome⟩ A =
      (postselectionInstrument h).branchOperator outcome
        (resourceConsumerChannel h hdegree A) := by sorry
