-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseRetry_finiteCyclicRetry_eight_target_hit_probability_one
-- name    : QEC.Distillation.PhaseRetry.finiteCyclicRetry_eight_target_hit_probability_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:02:27.314968+00:00
-- url     : https://prove2.me/theorems/9d94b6b1-1f10-4d50-940d-ecfe8a57bd2e
-- title:
--   Phase Retry: finite Cyclic Retry eight target hit probability one
-- statement:
--   The actual order-eight finite retry walk hits every target with probability one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseRetry.lean#L440-L447
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseRetry.lean#L440-L447

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section

theorem QEC.Distillation.PhaseRetry.finiteCyclicRetry_eight_target_hit_probability_one (start target : ZMod 8) :
    Filter.Tendsto (fun blocks => targetHitProbability 8 blocks start target)
      Filter.atTop (nhds 1) := by sorry
