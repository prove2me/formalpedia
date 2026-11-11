-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseAmplitude_neg_pi_div_eight
-- name    : QEC.Distillation.OneQubitMagic.phaseAmplitude_neg_pi_div_eight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:11:40.317351+00:00
-- url     : https://prove2.me/theorems/27f5422c-a150-4c70-ab3f-0981415bdde4
-- title:
--   One Qubit Magic: phase Amplitude neg pi div eight
-- statement:
--   The One Qubit Magic construction uses the phase Amplitude neg pi div eight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/HResourcePhase.lean#L215-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/HResourcePhase.lean#L215-L230

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit

theorem QEC.Distillation.OneQubitMagic.phaseAmplitude_neg_pi_div_eight :
    phaseAmplitude (-Real.pi / 8) =
      (Real.cos (Real.pi / 8) : Complex) -
        (Real.sin (Real.pi / 8) : Complex) * Complex.I := by sorry
