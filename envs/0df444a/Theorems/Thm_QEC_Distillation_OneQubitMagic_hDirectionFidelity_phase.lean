-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_hDirectionFidelity_phase
-- name    : QEC.Distillation.OneQubitMagic.hDirectionFidelity_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:11:17.024973+00:00
-- url     : https://prove2.me/theorems/4bb99fb9-befa-4930-8804-cd2b338596bf
-- title:
--   One Qubit Magic: h Direction Fidelity phase
-- statement:
--   The One Qubit Magic construction uses the h Direction Fidelity phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L890-L896
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L890-L896

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit

theorem QEC.Distillation.OneQubitMagic.hDirectionFidelity_phase
    (rho : DensityOperator QubitSpace) (d : HDirection) :
    hDirectionFidelity (phaseTransport.conjDensity rho)
        (phaseClifford • d) =
      hDirectionFidelity rho d := by sorry
