-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_rankOne_ensemble_trace_one
-- name    : QEC.Distillation.OneQubitMagic.rankOne_ensemble_trace_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:05:59.698916+00:00
-- url     : https://prove2.me/theorems/fb2a5540-46c6-4a30-b327-cc592fd2330d
-- title:
--   One Qubit Magic: rank One ensemble trace one
-- statement:
--   The One Qubit Magic construction uses the rank One ensemble trace one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L644-L652
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L644-L652

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit

theorem QEC.Distillation.OneQubitMagic.rankOne_ensemble_trace_one
    (rho : DensityOperator QubitSpace) {m : Nat}
    (u : Fin m → QubitSpace)
    (hensemble : rho.toOperator =
      ∑ i, (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap) :
    ∑ i, inner Complex (u i) (u i) = 1 := by sorry
