-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_trace_mul_rankOne
-- name    : QEC.Distillation.OneQubitMagic.trace_mul_rankOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:09:31.808356+00:00
-- url     : https://prove2.me/theorems/59f0d921-a456-42cf-b4ec-ea83ff7b3289
-- title:
--   One Qubit Magic: trace mul rank One
-- statement:
--   The One Qubit Magic construction uses the trace mul rank One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L664-L676
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L664-L676

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit

theorem QEC.Distillation.OneQubitMagic.trace_mul_rankOne
    (P : Operator QubitSpace) (u : QubitSpace) :
    LinearMap.trace Complex QubitSpace
      (P * (InnerProductSpace.rankOne Complex u u).toLinearMap) =
      inner Complex u (P u) := by sorry
