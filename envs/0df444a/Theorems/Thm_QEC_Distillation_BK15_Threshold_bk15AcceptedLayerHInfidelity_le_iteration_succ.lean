-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15AcceptedLayerHInfidelity_le_iteration_succ
-- name    : QEC.Distillation.BK15.Threshold.bk15AcceptedLayerHInfidelity_le_iteration_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T04:28:22.915052+00:00
-- url     : https://prove2.me/theorems/e8ad244f-471f-4804-bbaa-933d38526aee
-- title:
--   Threshold: bk15 Accepted Layer HInfidelity le iteration succ
-- statement:
--   The genuine returned H density of an actual scheduled accepted layer has
--   H-infidelity bounded by the next accepted-error iterate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L1178-L1194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L1178-L1194

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic

theorem QEC.Distillation.BK15.Threshold.bk15AcceptedLayerHInfidelity_le_iteration_succ
    (epsilon : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) (rounds : Nat) :
    1 - hFidelity
        (bk15AcceptedLayerHOutput epsilon hpositive hthreshold rounds) ^ 2 <=
      bk15Iteration epsilon (rounds + 1) := by sorry
