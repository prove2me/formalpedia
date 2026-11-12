-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_density_toOperator_eq_blochProjector
-- name    : QEC.Distillation.OneQubitMagic.density_toOperator_eq_blochProjector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:09:15.888785+00:00
-- url     : https://prove2.me/theorems/e9a2220b-98f3-48c7-89d7-b1a12c112b14
-- title:
--   One Qubit Magic: density to Operator eq bloch Projector
-- statement:
--   Every mixed one-qubit density has its exact Pauli/Bloch expansion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L195-L265
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L195-L265

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit

theorem QEC.Distillation.OneQubitMagic.density_toOperator_eq_blochProjector
    (rho : DensityOperator QubitSpace) :
    rho.toOperator = blochProjector (densityBloch rho) := by sorry
