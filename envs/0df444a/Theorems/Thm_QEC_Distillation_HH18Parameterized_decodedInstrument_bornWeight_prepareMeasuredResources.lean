-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedInstrument_bornWeight_prepareMeasuredResources
-- name    : QEC.Distillation.HH18Parameterized.decodedInstrument_bornWeight_prepareMeasuredResources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:59:55.277643+00:00
-- url     : https://prove2.me/theorems/2d08bde6-09c6-4edc-a303-e52cc35c1d5e
-- title:
--   HH18 Parameterized: decoded Instrument born Weight prepare Measured Resources
-- statement:
--   On the actual measured-resource record, each decoded visible Born weight
--   is exactly the existing physical endpoint weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrument.lean#L186-L195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrument.lean#L186-L195

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

theorem QEC.Distillation.HH18Parameterized.decodedInstrument_bornWeight_prepareMeasuredResources {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace)
    (outcome : DistillationOutcome) :
    (decodedInstrument h hdegree).bornWeight outcome
        (prepareMeasuredResources m w inputs) =
      endpointWeight h hdegree inputs outcome := by sorry
