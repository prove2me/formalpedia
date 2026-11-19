-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_successProbability
-- name    : QEC.Distillation.BK15.Protocol.bk15Run_successProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T02:07:35.197626+00:00
-- url     : https://prove2.me/theorems/9ef59323-9140-4667-81c7-9abdb8025bd8
-- title:
--   Protocol: bk15 Run success Probability
-- statement:
--   The Protocol construction uses the bk15 Run success Probability property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Protocol.lean#L2384-L2388
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Protocol.lean#L2384-L2388

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

theorem QEC.Distillation.BK15.Protocol.bk15Run_successProbability (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) :
    (bk15Run epsilon hpositive).successProbability =
      endpointWeight epsilon .accepted := by sorry

attribute [defeq] QEC.Distillation.BK15.Protocol.bk15Run_successProbability
