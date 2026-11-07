-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenWeight_eq_zero_iff
-- name    : QEC.Distillation.TwoQubit.zzEvenWeight_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:23:52.084246+00:00
-- url     : https://prove2.me/theorems/34a4ef3b-cc96-4405-b171-ca2d6b25348a
-- title:
--   Two Qubit: zz Even Weight eq zero iff
-- statement:
--   The Two Qubit construction uses the zz Even Weight eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityWeights.lean#L93-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityWeights.lean#L93-L95

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open scoped InnerProductSpace

theorem QEC.Distillation.TwoQubit.zzEvenWeight_eq_zero_iff (psi : TwoQubitSpace) :
    zzEvenWeight psi = 0 ↔ zzEvenProjector psi = 0 := by sorry
