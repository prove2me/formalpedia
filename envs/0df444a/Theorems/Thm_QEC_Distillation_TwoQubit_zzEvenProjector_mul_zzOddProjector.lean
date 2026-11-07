-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenProjector_mul_zzOddProjector
-- name    : QEC.Distillation.TwoQubit.zzEvenProjector_mul_zzOddProjector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:00:20.424639+00:00
-- url     : https://prove2.me/theorems/e0706636-1d84-44c6-b0bc-93dc9bd20383
-- title:
--   Two Qubit: zz Even Projector mul zz Odd Projector
-- statement:
--   The Two Qubit construction uses the zz Even Projector mul zz Odd Projector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Parity.lean#L116-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Parity.lean#L116-L121

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics Semantics.Qubit

theorem QEC.Distillation.TwoQubit.zzEvenProjector_mul_zzOddProjector :
    zzEvenProjector * zzOddProjector = (0 : Operator TwoQubitSpace) := by sorry
