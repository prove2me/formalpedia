-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Protocol_oneSiteWord_l2Syndrome_ne_zero
-- name    : QEC.Distillation.BK15.Protocol.oneSiteWord_l2Syndrome_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T02:07:41.322544+00:00
-- url     : https://prove2.me/theorems/4f311163-a22f-49d6-b86e-4b4c3fe41c4e
-- title:
--   Protocol: one Site Word l2 Syndrome ne zero
-- statement:
--   Every one-site word has a nonzero first-stage syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Protocol.lean#L255-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Protocol.lean#L255-L257

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

theorem QEC.Distillation.BK15.Protocol.oneSiteWord_l2Syndrome_ne_zero (site : Fin 15) :
    l2Syndrome (oneSiteWord site) ≠ 0 := by sorry
