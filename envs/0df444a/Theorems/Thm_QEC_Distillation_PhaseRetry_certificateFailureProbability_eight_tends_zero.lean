-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseRetry_certificateFailureProbability_eight_tends_zero
-- name    : QEC.Distillation.PhaseRetry.certificateFailureProbability_eight_tends_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:02:20.386978+00:00
-- url     : https://prove2.me/theorems/faaaf08e-d1e2-4c1a-b1ff-ab819c61431a
-- title:
--   Phase Retry: certificate Failure Probability eight tends zero
-- statement:
--   The exact order-eight finite-sample certificate failure probability vanishes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseRetry.lean#L384-L393
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseRetry.lean#L384-L393

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section

theorem QEC.Distillation.PhaseRetry.certificateFailureProbability_eight_tends_zero :
    AlmostSureTargetHit (certificateFailureProbability 8) := by sorry
