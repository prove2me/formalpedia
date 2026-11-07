-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseRetry_almostSureTargetHit_of_le_certificateTail
-- name    : QEC.Distillation.PhaseRetry.almostSureTargetHit_of_le_certificateTail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:36:45.066444+00:00
-- url     : https://prove2.me/theorems/7cd7026f-05bf-4222-b93d-6d30515df3c9
-- title:
--   Phase Retry: almost Sure Target Hit of le certificate Tail
-- statement:
--   Any nonnegative tail below a vanishing certificate tail also vanishes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseRetry.lean#L358-L365
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseRetry.lean#L358-L365

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section

theorem QEC.Distillation.PhaseRetry.almostSureTargetHit_of_le_certificateTail
    {q : Nat} {failure : Nat → Real}
    (hNonnegative : ∀ blocks, 0 ≤ failure blocks)
    (hBound : ∀ blocks, failure blocks ≤ certificateFailureTail q blocks)
    (hTail : AlmostSureTargetHit (certificateFailureTail q)) :
    AlmostSureTargetHit failure := by sorry
