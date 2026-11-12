-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_decodedErrorBranch_toOperator
-- name    : QEC.Distillation.HH18Protocol.decodedErrorBranch_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:25:58.101325+00:00
-- url     : https://prove2.me/theorems/e274ba41-4f40-454c-af1c-ec3ddbaa2248
-- title:
--   HH18 Protocol: decoded Error Branch to Operator
-- statement:
--   The HH18 Protocol construction uses the decoded Error Branch to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/DecodedErrorBridge.lean#L65-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/DecodedErrorBridge.lean#L65-L71

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

theorem QEC.Distillation.HH18Protocol.decodedErrorBranch_toOperator (error : PhysicalErrorWord) :
    (decodedErrorBranch error).toOperator =
      decoderChannel (HH18SyndromeDecoding.errorBranchOperator error) := by sorry
