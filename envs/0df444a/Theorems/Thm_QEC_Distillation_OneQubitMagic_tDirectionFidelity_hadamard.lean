-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_tDirectionFidelity_hadamard
-- name    : QEC.Distillation.OneQubitMagic.tDirectionFidelity_hadamard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:10:56.637367+00:00
-- url     : https://prove2.me/theorems/c2d86f98-ab28-45e5-bfcb-8f902e26fd51
-- title:
--   One Qubit Magic: t Direction Fidelity hadamard
-- statement:
--   The One Qubit Magic construction uses the t Direction Fidelity hadamard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L866-L872
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L866-L872

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit

theorem QEC.Distillation.OneQubitMagic.tDirectionFidelity_hadamard
    (rho : DensityOperator QubitSpace) (d : TDirection) :
    tDirectionFidelity (hadamardTransport.conjDensity rho)
        (hadamardClifford • d) =
      tDirectionFidelity rho d := by sorry
