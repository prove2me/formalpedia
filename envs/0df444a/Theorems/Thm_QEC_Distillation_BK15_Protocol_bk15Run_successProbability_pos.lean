-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_successProbability_pos
-- name    : QEC.Distillation.BK15.Protocol.bk15Run_successProbability_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T02:07:21.174479+00:00
-- url     : https://prove2.me/theorems/eebf3abf-d820-4d8e-8978-d6efb6980764
-- title:
--   Protocol: bk15 Run success Probability pos
-- statement:
--   The packaged success probability is genuinely positive in the strict
--   source interval.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Protocol.lean#L2392-L2395
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Protocol.lean#L2392-L2395

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

theorem QEC.Distillation.BK15.Protocol.bk15Run_successProbability_pos (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) :
    0 < (bk15Run epsilon hpositive).successProbability := by sorry
