-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseAmplitude_two_pi_mul_int
-- name    : QEC.Distillation.OneQubitMagic.phaseAmplitude_two_pi_mul_int
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:26:41.531878+00:00
-- url     : https://prove2.me/theorems/c62055d0-6bc2-4328-af55-6c5f7caaee1e
-- title:
--   One Qubit Magic: phase Amplitude two pi mul int
-- statement:
--   Integer multiples of one full turn have trivial phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitPhase.lean#L36-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitPhase.lean#L36-L41

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit

theorem QEC.Distillation.OneQubitMagic.phaseAmplitude_two_pi_mul_int (k : Int) :
    phaseAmplitude ((2 * Real.pi) * (k : Real)) = 1 := by sorry
