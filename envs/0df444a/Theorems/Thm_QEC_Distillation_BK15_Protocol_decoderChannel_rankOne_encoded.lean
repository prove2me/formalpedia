-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Protocol_decoderChannel_rankOne_encoded
-- name    : QEC.Distillation.BK15.Protocol.decoderChannel_rankOne_encoded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T02:07:44.360199+00:00
-- url     : https://prove2.me/theorems/bdaf2438-dd79-414f-85ee-73077447c206
-- title:
--   Protocol: decoder Channel rank One encoded
-- statement:
--   The Protocol construction uses the decoder Channel rank One encoded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Protocol.lean#L1441-L1463
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Protocol.lean#L1441-L1463

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_FifteenQubitH_Protocol
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Protocol
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open NoisyInput
open scoped BigOperators TensorProduct
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.BK15.Protocol.decoderChannel_rankOne_encoded (psi : LogicalRegister) :
    decoderChannel (InnerProductSpace.rankOne Complex
      (ambientEncodingIsometry psi) (ambientEncodingIsometry psi)).toLinearMap =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by sorry
