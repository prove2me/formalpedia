-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_zzOddWeight_eq_zero_iff
-- name    : QEC.Distillation.TwoQubit.zzOddWeight_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:23:47.719924+00:00
-- url     : https://prove2.me/theorems/1faec129-b10a-4852-89b5-9a6b4fea55c8
-- title:
--   Two Qubit: zz Odd Weight eq zero iff
-- statement:
--   The Two Qubit construction uses the zz Odd Weight eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityWeights.lean#L97-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityWeights.lean#L97-L99

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open scoped InnerProductSpace

theorem QEC.Distillation.TwoQubit.zzOddWeight_eq_zero_iff (psi : TwoQubitSpace) :
    zzOddWeight psi = 0 ↔ zzOddProjector psi = 0 := by sorry
