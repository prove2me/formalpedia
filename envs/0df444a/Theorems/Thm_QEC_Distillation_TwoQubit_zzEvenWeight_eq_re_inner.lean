-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenWeight_eq_re_inner
-- name    : QEC.Distillation.TwoQubit.zzEvenWeight_eq_re_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:23:13.241211+00:00
-- url     : https://prove2.me/theorems/ac8c04e2-548f-4bf7-b328-1b0ae26fb23c
-- title:
--   Two Qubit: zz Even Weight eq re inner
-- statement:
--   The Two Qubit construction uses the zz Even Weight eq re inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityWeights.lean#L22-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityWeights.lean#L22-L37

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open scoped InnerProductSpace

theorem QEC.Distillation.TwoQubit.zzEvenWeight_eq_re_inner (psi : TwoQubitSpace) :
    zzEvenWeight psi =
      Complex.re ⟪psi, zzEvenProjector psi⟫_ℂ := by sorry
