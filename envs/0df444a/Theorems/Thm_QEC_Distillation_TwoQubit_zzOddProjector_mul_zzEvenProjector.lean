-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_mul_zzEvenProjector
-- name    : QEC.Distillation.TwoQubit.zzOddProjector_mul_zzEvenProjector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:00:23.663289+00:00
-- url     : https://prove2.me/theorems/d2859802-ea4e-4953-9011-c1d87fd86b34
-- title:
--   Two Qubit: zz Odd Projector mul zz Even Projector
-- statement:
--   The Two Qubit construction uses the zz Odd Projector mul zz Even Projector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Parity.lean#L123-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Parity.lean#L123-L128

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics Semantics.Qubit

theorem QEC.Distillation.TwoQubit.zzOddProjector_mul_zzEvenProjector :
    zzOddProjector * zzEvenProjector = (0 : Operator TwoQubitSpace) := by sorry
