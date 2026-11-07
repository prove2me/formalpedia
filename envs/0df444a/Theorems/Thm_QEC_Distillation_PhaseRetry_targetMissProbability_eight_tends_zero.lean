-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseRetry_targetMissProbability_eight_tends_zero
-- name    : QEC.Distillation.PhaseRetry.targetMissProbability_eight_tends_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:40:02.499855+00:00
-- url     : https://prove2.me/theorems/9f627693-1021-4b78-bba0-18e05c260be1
-- title:
--   Phase Retry: target Miss Probability eight tends zero
-- statement:
--   The actual order-eight target-miss probability tends to zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseRetry.lean#L408-L421
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseRetry.lean#L408-L421

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section

theorem QEC.Distillation.PhaseRetry.targetMissProbability_eight_tends_zero (start target : ZMod 8) :
    AlmostSureTargetHit (fun blocks => targetMissProbability 8 blocks start target) := by sorry
