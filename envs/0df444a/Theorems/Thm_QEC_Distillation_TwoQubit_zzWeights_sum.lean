-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_zzWeights_sum
-- name    : QEC.Distillation.TwoQubit.zzWeights_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:23:34.898191+00:00
-- url     : https://prove2.me/theorems/a39a4a43-ad60-4a12-80fb-ac1e3bc77ec0
-- title:
--   Two Qubit: zz Weights sum
-- statement:
--   The Two Qubit construction uses the zz Weights sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityWeights.lean#L64-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityWeights.lean#L64-L83

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open scoped InnerProductSpace

theorem QEC.Distillation.TwoQubit.zzWeights_sum (psi : TwoQubitSpace) :
    zzEvenWeight psi + zzOddWeight psi = ‖psi‖ ^ 2 := by sorry
