-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedInstrument_observe
-- name    : QEC.Distillation.HH18Parameterized.decodedInstrument_observe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:31:07.618198+00:00
-- url     : https://prove2.me/theorems/24c3d968-13b2-4547-8a12-32d394d86135
-- title:
--   HH18 Parameterized: decoded Instrument observe
-- statement:
--   The visible observation is exactly the real postselection outcome of the
--   retained syndrome branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrument.lean#L98-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrument.lean#L98-L103

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

theorem QEC.Distillation.HH18Parameterized.decodedInstrument_observe {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (index : decodedRawIndex h hdegree) :
    (decodedInstrument h hdegree).observe index =
      (postselectionInstrument h).observe index.1.2 := by sorry
