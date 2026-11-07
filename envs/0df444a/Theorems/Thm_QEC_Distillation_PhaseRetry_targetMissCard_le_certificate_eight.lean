-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseRetry_targetMissCard_le_certificate_eight
-- name    : QEC.Distillation.PhaseRetry.targetMissCard_le_certificate_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:39:50.335212+00:00
-- url     : https://prove2.me/theorems/2fa7321b-b776-4cf9-9b20-05a4a4fe223f
-- title:
--   Phase Retry: target Miss Card le certificate eight
-- statement:
--   An actual order-eight target miss has no all-positive block, hence injects into it.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseRetry.lean#L270-L292
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseRetry.lean#L270-L292

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section

theorem QEC.Distillation.PhaseRetry.targetMissCard_le_certificate_eight (start target : ZMod 8) (blocks : Nat) :
    @Fintype.card (TargetMissTrace 8 blocks start target)
      (targetMissTraceFintype 8 blocks start target) ≤
      Fintype.card (NoPositiveTrace 8 blocks) := by sorry
