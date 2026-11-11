-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_tProjector
-- name    : QEC.Distillation.OneQubitMagic.phase_conj_tProjector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:01:09.403533+00:00
-- url     : https://prove2.me/theorems/2fd3b034-a05f-4b4e-aee5-b60b7ddd1e68
-- title:
--   One Qubit Magic: phase conj t Projector
-- statement:
--   The One Qubit Magic construction uses the phase conj t Projector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L151-L155
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L151-L155

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit

theorem QEC.Distillation.OneQubitMagic.phase_conj_tProjector (d : TDirection) :
    phaseTransport.conjOperator (tProjector d) =
      tProjector (phaseClifford • d) := by sorry
