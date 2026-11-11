-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_pauliX
-- name    : QEC.Distillation.OneQubitMagic.phase_conj_pauliX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:59:36.573322+00:00
-- url     : https://prove2.me/theorems/6b415f75-a951-4ab9-b638-faef9c6ff4f3
-- title:
--   One Qubit Magic: phase conj pauli X
-- statement:
--   Concrete `S X S⁻¹ = Y`, giving the X contribution in `phaseClifford`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitClifford.lean#L437-L442
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitClifford.lean#L437-L442

import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open scoped BigOperators
noncomputable section

theorem QEC.Distillation.OneQubitMagic.phase_conj_pauliX :
    phaseTransport.conjOperator pauliX = pauliY := by sorry
