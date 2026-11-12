-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_decoderChannel_rankOne_encoded
-- name    : QEC.Distillation.HH18Protocol.decoderChannel_rankOne_encoded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:58:28.932451+00:00
-- url     : https://prove2.me/theorems/a6767093-6e1a-4669-9df4-ed2053986d5a
-- title:
--   HH18 Protocol: decoder Channel rank One encoded
-- statement:
--   The HH18 Protocol construction uses the decoder Channel rank One encoded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Decoder.lean#L213-L235
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Decoder.lean#L213-L235

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalTypes
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Decoder
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

theorem QEC.Distillation.HH18Protocol.decoderChannel_rankOne_encoded (psi : LogicalRegister) :
    decoderChannel (InnerProductSpace.rankOne Complex
      (ambientEncodingIsometry psi) (ambientEncodingIsometry psi)).toLinearMap =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by sorry
