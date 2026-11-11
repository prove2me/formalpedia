-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
-- name    : QEC.Distillation.OneQubitMagic.phase_conj_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:16:25.954247+00:00
-- url     : https://prove2.me/theorems/bd69f086-ba58-4b7e-9bd5-3d6d15dc65c0
-- title:
--   One Qubit Magic: phase conj one
-- statement:
--   Phase fixes the identity operator under conjugation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitClifford.lean#L405-L407
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitClifford.lean#L405-L407

import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open scoped BigOperators
noncomputable section

theorem QEC.Distillation.OneQubitMagic.phase_conj_one :
    phaseTransport.conjOperator (1 : Operator QubitSpace) = 1 := by sorry
