-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseRetry_finiteCyclicRetry_twelve_target_hit_probability_one
-- name    : QEC.Distillation.PhaseRetry.finiteCyclicRetry_twelve_target_hit_probability_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:04:32.121223+00:00
-- url     : https://prove2.me/theorems/93438d96-75b0-4fcb-8abe-851cd2e4e150
-- title:
--   Phase Retry: finite Cyclic Retry twelve target hit probability one
-- statement:
--   The actual order-twelve finite retry walk hits every target with probability one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseRetry.lean#L450-L457
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseRetry.lean#L450-L457

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section

theorem QEC.Distillation.PhaseRetry.finiteCyclicRetry_twelve_target_hit_probability_one (start target : ZMod 12) :
    Filter.Tendsto (fun blocks => targetHitProbability 12 blocks start target)
      Filter.atTop (nhds 1) := by sorry
