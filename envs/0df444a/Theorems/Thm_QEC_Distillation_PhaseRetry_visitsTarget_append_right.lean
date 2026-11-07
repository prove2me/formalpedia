-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseRetry_visitsTarget_append_right
-- name    : QEC.Distillation.PhaseRetry.visitsTarget_append_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:36:26.707489+00:00
-- url     : https://prove2.me/theorems/6b2dcbc1-1d85-490f-bab0-eac00fe24a69
-- title:
--   Phase Retry: visits Target append right
-- statement:
--   A target reached after a retry suffix is reached in the whole trace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseRetry.lean#L59-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseRetry.lean#L59-L70

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section

theorem QEC.Distillation.PhaseRetry.visitsTarget_append_right {q : Nat} {start target : ZMod q}
    (history suffix : List Bool)
    (h : visitsTarget (endpoint start history) target suffix) :
    visitsTarget start target (history ++ suffix) := by sorry
