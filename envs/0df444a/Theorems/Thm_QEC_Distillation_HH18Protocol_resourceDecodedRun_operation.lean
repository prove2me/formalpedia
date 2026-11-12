-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_resourceDecodedRun_operation
-- name    : QEC.Distillation.HH18Protocol.resourceDecodedRun_operation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:25:26.442139+00:00
-- url     : https://prove2.me/theorems/fcb715b2-148c-4bfb-be6f-a00f8821cd02
-- title:
--   HH18 Protocol: resource Decoded Run operation
-- statement:
--   The HH18 Protocol construction uses the resource Decoded Run operation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/NormalizedRun.lean#L156-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/NormalizedRun.lean#L156-L159

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

theorem QEC.Distillation.HH18Protocol.resourceDecodedRun_operation
    (inputs : ResourceInput resourceCount QubitSpace) :
    (resourceDecodedRun inputs).operation = decodedOperation := by sorry
