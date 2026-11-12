-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_resourcePostselectionInstrument_bornWeight
-- name    : QEC.Distillation.HH18Parameterized.resourcePostselectionInstrument_bornWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:01:51.991706+00:00
-- url     : https://prove2.me/theorems/2a63e4dc-d683-4ae8-900a-6f14c8eca1f0
-- title:
--   HH18 Parameterized: resource Postselection Instrument born Weight
-- statement:
--   The resource-and-postselection instrument has precisely the coarse
--   postselection Born weight after the actual resource channel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrument.lean#L156-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrument.lean#L156-L165

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

theorem QEC.Distillation.HH18Parameterized.resourcePostselectionInstrument_bornWeight {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (outcome : DistillationOutcome) (rho : DensityOperator (PhysicalRegister m w)) :
    (resourcePostselectionInstrument h hdegree).bornWeight
        ⟨PUnit.unit, outcome⟩ rho =
      postselectionWeight h outcome
        ((resourceConsumerChannel h hdegree).mapDensity rho) := by sorry
