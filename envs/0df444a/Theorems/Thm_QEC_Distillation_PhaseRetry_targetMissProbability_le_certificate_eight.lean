-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseRetry_targetMissProbability_le_certificate_eight
-- name    : QEC.Distillation.PhaseRetry.targetMissProbability_le_certificate_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:36:38.379201+00:00
-- url     : https://prove2.me/theorems/aec08e03-833d-496f-976d-da79891e214a
-- title:
--   Phase Retry: target Miss Probability le certificate eight
-- statement:
--   The actual order-eight miss probability is bounded by the exact certificate tail.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseRetry.lean#L320-L325
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseRetry.lean#L320-L325

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section

theorem QEC.Distillation.PhaseRetry.targetMissProbability_le_certificate_eight (start target : ZMod 8) (blocks : Nat) :
    targetMissProbability 8 blocks start target ≤ certificateFailureProbability 8 blocks := by sorry
