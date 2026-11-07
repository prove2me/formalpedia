-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_apply_basis
-- name    : QEC.Distillation.TwoQubit.zzOddProjector_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:22:40.798689+00:00
-- url     : https://prove2.me/theorems/754ea310-7e96-451d-b67c-256dc987e920
-- title:
--   Two Qubit: zz Odd Projector apply basis
-- statement:
--   The Two Qubit construction uses the zz Odd Projector apply basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Parity.lean#L162-L185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Parity.lean#L162-L185

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics Semantics.Qubit

theorem QEC.Distillation.TwoQubit.zzOddProjector_apply_basis (bits : Bitstring (Fin 2)) :
    zzOddProjector
        (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits) =
      if bits 0 = bits 1 then 0
      else EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits := by sorry
