-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_zzWeights_sum_of_normSq_one
-- name    : QEC.Distillation.TwoQubit.zzWeights_sum_of_normSq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:01:09.738161+00:00
-- url     : https://prove2.me/theorems/789b1510-b38c-45ec-baa3-33582ab240f1
-- title:
--   Two Qubit: zz Weights sum of norm Sq one
-- statement:
--   The Two Qubit construction uses the zz Weights sum of norm Sq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityWeights.lean#L85-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityWeights.lean#L85-L91

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open scoped InnerProductSpace

theorem QEC.Distillation.TwoQubit.zzWeights_sum_of_normSq_one
    (psi : TwoQubitSpace) (hpsi : ‖psi‖ ^ 2 = 1) :
    zzEvenWeight psi + zzOddWeight psi = 1 := by sorry
