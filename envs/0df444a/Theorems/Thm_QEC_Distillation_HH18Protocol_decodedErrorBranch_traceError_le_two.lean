-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_decodedErrorBranch_traceError_le_two
-- name    : QEC.Distillation.HH18Protocol.decodedErrorBranch_traceError_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:25:36.624661+00:00
-- url     : https://prove2.me/theorems/e0a86c44-ff96-45a8-a14a-fa8a9e4704e2
-- title:
--   HH18 Protocol: decoded Error Branch trace Error le two
-- statement:
--   Every decoded physical-error branch lies within trace norm two of the
--   ideal density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/DecodedErrorBridge.lean#L75-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/DecodedErrorBridge.lean#L75-L88

import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Decoder
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NormalizedRun
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_DecodedErrorBridge
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u v w
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instDecodedBridgeClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instDecodedBridgeClassicalDecidable

theorem QEC.Distillation.HH18Protocol.decodedErrorBranch_traceError_le_two (error : PhysicalErrorWord) :
    hh18OutputTraceError (decodedErrorBranch error) idealLogicalTOutput ≤ 2 := by sorry
