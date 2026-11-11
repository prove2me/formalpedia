-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
-- name    : QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:01:58.412198+00:00
-- url     : https://prove2.me/theorems/1136461d-aced-428c-98ae-9b1c6a93cceb
-- title:
--   One Qubit Magic: phase Shift Linear Equiv symm apply
-- statement:
--   The One Qubit Magic construction uses the phase Shift Linear Equiv symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitPhase.lean#L279-L283
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitPhase.lean#L279-L283

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit

theorem QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
    (theta : Real) (psi : QubitSpace) :
    (phaseShiftLinearEquiv theta).symm psi =
      phaseShiftOperator (-theta) psi := by sorry

attribute [defeq] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
