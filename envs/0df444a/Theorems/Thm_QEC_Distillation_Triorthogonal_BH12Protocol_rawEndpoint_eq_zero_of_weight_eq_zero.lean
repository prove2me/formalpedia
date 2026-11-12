-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_rawEndpoint_eq_zero_of_weight_eq_zero
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.rawEndpoint_eq_zero_of_weight_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:43:46.721904+00:00
-- url     : https://prove2.me/theorems/9539d14b-10a8-450d-a9b6-52d66c2b3077
-- title:
--   BH12 Protocol: raw Endpoint eq zero of weight eq zero
-- statement:
--   A zero-weight endpoint is the literal zero raw operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L209-L213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L209-L213

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12Protocol
open Semantics
open Coding
open Coding.PauliSymplectic
open BH12EvenFamily
open BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem QEC.Distillation.Triorthogonal.BH12Protocol.rawEndpoint_eq_zero_of_weight_eq_zero (q : Nat) (p : ErrorParameter)
    (outcome : DistillationOutcome) (hzero : endpointWeight q p outcome = 0) :
    rawEndpoint q p outcome = 0 := by sorry
