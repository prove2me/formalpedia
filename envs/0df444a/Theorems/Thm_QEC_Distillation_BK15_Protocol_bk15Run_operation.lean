-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_operation
-- name    : QEC.Distillation.BK15.Protocol.bk15Run_operation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T02:07:36.518464+00:00
-- url     : https://prove2.me/theorems/0b1e3d96-e197-475d-8581-a323716a448b
-- title:
--   Protocol: bk15 Run operation
-- statement:
--   The Protocol construction uses the bk15 Run operation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Protocol.lean#L2379-L2382
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Protocol.lean#L2379-L2382

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

theorem QEC.Distillation.BK15.Protocol.bk15Run_operation (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) :
    (bk15Run epsilon hpositive).operation = decodedOperation := by sorry

attribute [defeq] QEC.Distillation.BK15.Protocol.bk15Run_operation
