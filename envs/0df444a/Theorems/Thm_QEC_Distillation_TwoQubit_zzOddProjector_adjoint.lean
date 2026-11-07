-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_adjoint
-- name    : QEC.Distillation.TwoQubit.zzOddProjector_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:21:51.023981+00:00
-- url     : https://prove2.me/theorems/6eb69f3e-db5b-43bc-81c6-348378ff414e
-- title:
--   Two Qubit: zz Odd Projector adjoint
-- statement:
--   The Two Qubit construction uses the zz Odd Projector adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Parity.lean#L81-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Parity.lean#L81-L90

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics Semantics.Qubit

theorem QEC.Distillation.TwoQubit.zzOddProjector_adjoint :
    LinearMap.adjoint zzOddProjector = zzOddProjector := by sorry
