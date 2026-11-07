-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_zzOddWeight_eq_re_inner
-- name    : QEC.Distillation.TwoQubit.zzOddWeight_eq_re_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:23:18.998134+00:00
-- url     : https://prove2.me/theorems/507c6073-4b6c-44c6-bf75-e78646834f07
-- title:
--   Two Qubit: zz Odd Weight eq re inner
-- statement:
--   The Two Qubit construction uses the zz Odd Weight eq re inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityWeights.lean#L39-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityWeights.lean#L39-L54

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open scoped InnerProductSpace

theorem QEC.Distillation.TwoQubit.zzOddWeight_eq_re_inner (psi : TwoQubitSpace) :
    zzOddWeight psi =
      Complex.re ⟪psi, zzOddProjector psi⟫_ℂ := by sorry
