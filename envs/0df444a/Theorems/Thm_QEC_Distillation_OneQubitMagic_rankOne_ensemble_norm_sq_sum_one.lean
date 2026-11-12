-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_rankOne_ensemble_norm_sq_sum_one
-- name    : QEC.Distillation.OneQubitMagic.rankOne_ensemble_norm_sq_sum_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:06:26.752198+00:00
-- url     : https://prove2.me/theorems/d734eb21-0f43-4cdb-be92-061e19795479
-- title:
--   One Qubit Magic: rank One ensemble norm sq sum one
-- statement:
--   The One Qubit Magic construction uses the rank One ensemble norm sq sum one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L654-L662
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L654-L662

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit

theorem QEC.Distillation.OneQubitMagic.rankOne_ensemble_norm_sq_sum_one
    (rho : DensityOperator QubitSpace) {m : Nat}
    (u : Fin m → QubitSpace)
    (hensemble : rho.toOperator =
      ∑ i, (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap) :
    ∑ i, ‖u i‖ ^ 2 = 1 := by sorry
