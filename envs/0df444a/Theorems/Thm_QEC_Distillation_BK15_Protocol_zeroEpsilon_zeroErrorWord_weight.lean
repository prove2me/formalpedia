-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Protocol_zeroEpsilon_zeroErrorWord_weight
-- name    : QEC.Distillation.BK15.Protocol.zeroEpsilon_zeroErrorWord_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T02:07:41.283236+00:00
-- url     : https://prove2.me/theorems/72bfc1c8-39fd-4c7e-9ecf-8d386e1f9326
-- title:
--   Protocol: zero Epsilon zero Error Word weight
-- statement:
--   The Protocol construction uses the zero Epsilon zero Error Word weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Protocol.lean#L2476-L2479
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Protocol.lean#L2476-L2479

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

theorem QEC.Distillation.BK15.Protocol.zeroEpsilon_zeroErrorWord_weight :
    bk15WordWeight zeroEpsilon zeroErrorWord = 1 := by sorry
