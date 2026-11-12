-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_hDirectionFidelity_hadamard
-- name    : QEC.Distillation.OneQubitMagic.hDirectionFidelity_hadamard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:10:59.381016+00:00
-- url     : https://prove2.me/theorems/e1cd511a-c753-4bef-adba-2155c1830f1a
-- title:
--   One Qubit Magic: h Direction Fidelity hadamard
-- statement:
--   The One Qubit Magic construction uses the h Direction Fidelity hadamard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L882-L888
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L882-L888

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit

theorem QEC.Distillation.OneQubitMagic.hDirectionFidelity_hadamard
    (rho : DensityOperator QubitSpace) (d : HDirection) :
    hDirectionFidelity (hadamardTransport.conjDensity rho)
        (hadamardClifford • d) =
      hDirectionFidelity rho d := by sorry
