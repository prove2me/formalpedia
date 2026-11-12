-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_resourcePostselectionInstrument_complete
-- name    : QEC.Distillation.HH18Parameterized.resourcePostselectionInstrument_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:01:12.293617+00:00
-- url     : https://prove2.me/theorems/28ff6cb9-2b6e-4df6-962e-4eddde61ca17
-- title:
--   HH18 Parameterized: resource Postselection Instrument complete
-- statement:
--   Completeness of the actual resource-consumption and postselection
--   instrument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrument.lean#L50-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrument.lean#L50-L57

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

theorem QEC.Distillation.HH18Parameterized.resourcePostselectionInstrument_complete {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    (resourcePostselectionInstrument h hdegree).kraus.Complete := by sorry
