-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseRetry_targetMissProbability_eight_exponential_bound
-- name    : QEC.Distillation.PhaseRetry.targetMissProbability_eight_exponential_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:01:56.776397+00:00
-- url     : https://prove2.me/theorems/5a8f50fd-dd9d-49a5-b5ea-26fce4ed5426
-- title:
--   Phase Retry: target Miss Probability eight exponential bound
-- statement:
--   The actual order-eight target-miss probability has the explicit exponential bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseRetry.lean#L336-L342
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseRetry.lean#L336-L342

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section

theorem QEC.Distillation.PhaseRetry.targetMissProbability_eight_exponential_bound
    (start target : ZMod 8) (blocks : Nat) :
    targetMissProbability 8 blocks start target ≤ (255 / 256 : Real) ^ blocks := by sorry
