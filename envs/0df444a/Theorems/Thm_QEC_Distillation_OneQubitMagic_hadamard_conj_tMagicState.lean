-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_tMagicState
-- name    : QEC.Distillation.OneQubitMagic.hadamard_conj_tMagicState
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:06:38.891249+00:00
-- url     : https://prove2.me/theorems/6cdd054a-8f45-4882-9eeb-a7fb8bc63ea6
-- title:
--   One Qubit Magic: hadamard conj t Magic State
-- statement:
--   The One Qubit Magic construction uses the hadamard conj t Magic State property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L538-L545
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L538-L545

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit

theorem QEC.Distillation.OneQubitMagic.hadamard_conj_tMagicState (d : TDirection) :
    hadamardTransport.conjDensity (tMagicStateOfDirection d) =
      tMagicStateOfDirection (hadamardClifford • d) := by sorry
