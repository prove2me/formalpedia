-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseRetry_finiteCyclicRetry_eight_hits_target
-- name    : QEC.Distillation.PhaseRetry.finiteCyclicRetry_eight_hits_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:01:36.799583+00:00
-- url     : https://prove2.me/theorems/2f6ba7fa-e082-4560-9d64-fa0b80c00107
-- title:
--   Phase Retry: finite Cyclic Retry eight hits target
-- statement:
--   Every order-eight cyclic retry certificate reaches its requested target.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseRetry.lean#L212-L215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseRetry.lean#L212-L215

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section

theorem QEC.Distillation.PhaseRetry.finiteCyclicRetry_eight_hits_target (start target : ZMod 8) :
    FiniteCyclicRetryHitsTarget 8 start target := by sorry
