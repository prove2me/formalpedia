-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceHDensity_toOperator
-- name    : QEC.Distillation.OneQubitMagic.sourceHDensity_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:07:38.145482+00:00
-- url     : https://prove2.me/theorems/151fdac1-9066-41f6-a5c6-32b539109a4a
-- title:
--   One Qubit Magic: source HDensity to Operator
-- statement:
--   The One Qubit Magic construction uses the source HDensity to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/HResourcePhase.lean#L65-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/HResourcePhase.lean#L65-L70

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit

theorem QEC.Distillation.OneQubitMagic.sourceHDensity_toOperator :
    sourceHDensity.toOperator =
      (InnerProductSpace.rankOne Complex sourceHState sourceHState).toLinearMap := by sorry
