-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedInstrument_complete
-- name    : QEC.Distillation.HH18Parameterized.decodedInstrument_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:00:31.070034+00:00
-- url     : https://prove2.me/theorems/20215ad9-f6aa-4ac5-9c50-af6fd7aeaf4c
-- title:
--   HH18 Parameterized: decoded Instrument complete
-- statement:
--   Coarsening only observations leaves the actual decoded Kraus family
--   complete.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrument.lean#L107-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrument.lean#L107-L110

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

theorem QEC.Distillation.HH18Parameterized.decodedInstrument_complete {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    (decodedInstrument h hdegree).kraus.Complete := by sorry
