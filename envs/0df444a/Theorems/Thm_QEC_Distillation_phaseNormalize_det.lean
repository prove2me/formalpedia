-- Prove2me | Theorems.Thm_QEC_Distillation_phaseNormalize_det
-- name    : QEC.Distillation.phaseNormalize_det
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T14:11:58.856465+00:00
-- url     : https://prove2.me/theorems/dfd570ae-5a38-4116-8a17-5c277a9dbc80
-- title:
--   Distillation: phase Normalize det
-- statement:
--   Phase normalization has determinant one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2AxisCircle.lean#L361-L373
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2AxisCircle.lean#L361-L373

import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality

theorem QEC.Distillation.phaseNormalize_det (U : SingleQubitGate) :
    (phaseNormalize U : SingleQubitMatrix).det = 1 := by sorry
