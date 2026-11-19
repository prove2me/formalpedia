-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Protocol_zeroEpsilon_cleanWeight
-- name    : QEC.Distillation.BK15.Protocol.zeroEpsilon_cleanWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T02:07:49.165349+00:00
-- url     : https://prove2.me/theorems/e4e779e8-8c0a-447d-a3b7-5be9ddeaa6f5
-- title:
--   Protocol: zero Epsilon clean Weight
-- statement:
--   The Protocol construction uses the zero Epsilon clean Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Protocol.lean#L2473-L2474
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Protocol.lean#L2473-L2474

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

theorem QEC.Distillation.BK15.Protocol.zeroEpsilon_cleanWeight : zeroEpsilon.cleanWeight = 1 := by sorry
