-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_resourceDecodedRun_acceptedOutput
-- name    : QEC.Distillation.HH18Protocol.resourceDecodedRun_acceptedOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:24:21.668719+00:00
-- url     : https://prove2.me/theorems/70527bf3-5960-490f-821d-6d584bf522ea
-- title:
--   HH18 Protocol: resource Decoded Run accepted Output
-- statement:
--   At positive accepted Born mass, the decoded run reports the actual
--   decoded accepted conditional, not its zero-mass technical completion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/NormalizedRun.lean#L163-L169
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/NormalizedRun.lean#L163-L169

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Decoder
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NormalizedRun
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instNormalizedRunClassicalDecidable

theorem QEC.Distillation.HH18Protocol.resourceDecodedRun_acceptedOutput
    (inputs : ResourceInput resourceCount QubitSpace)
    (hpos : 0 < endpointWeight inputs .accepted) :
    (resourceDecodedRun inputs).acceptedOutput =
      decoderChannel.mapDensity (endpointConditional inputs .accepted hpos) := by sorry
