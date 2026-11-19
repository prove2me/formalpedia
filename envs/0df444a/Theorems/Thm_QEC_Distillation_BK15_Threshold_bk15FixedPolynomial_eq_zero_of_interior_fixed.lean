-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15FixedPolynomial_eq_zero_of_interior_fixed
-- name    : QEC.Distillation.BK15.Threshold.bk15FixedPolynomial_eq_zero_of_interior_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:25:37.482245+00:00
-- url     : https://prove2.me/theorems/f710f8fe-9e87-4cf6-9345-9b69282ddc61
-- title:
--   Threshold: bk15 Fixed Polynomial eq zero of interior fixed
-- statement:
--   The Threshold construction uses the bk15 Fixed Polynomial eq zero of interior fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L80-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L80-L104

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic

theorem QEC.Distillation.BK15.Threshold.bk15FixedPolynomial_eq_zero_of_interior_fixed
    {epsilon : Real} (hhalf : epsilon < 1 / 2)
    (hfixed : bk15Recurrence epsilon = epsilon) :
    bk15FixedPolynomial (bk15Bias epsilon) = 0 := by sorry
