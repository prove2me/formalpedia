-- Prove2me | Theorems.Thm_QEC_Distillation_phaseNormalize_matrix
-- name    : QEC.Distillation.phaseNormalize_matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:10:03.095329+00:00
-- url     : https://prove2.me/theorems/89cb5a93-41fc-4847-b07d-71e24be76228
-- title:
--   Distillation: phase Normalize matrix
-- statement:
--   The Distillation construction uses the phase Normalize matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2AxisCircle.lean#L356-L358
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2AxisCircle.lean#L356-L358

import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality

theorem QEC.Distillation.phaseNormalize_matrix (U : SingleQubitGate) :
    (phaseNormalize U : SingleQubitMatrix) = (determinantRoot U)⁻¹ • (U : SingleQubitMatrix) := by sorry

attribute [defeq] QEC.Distillation.phaseNormalize_matrix
