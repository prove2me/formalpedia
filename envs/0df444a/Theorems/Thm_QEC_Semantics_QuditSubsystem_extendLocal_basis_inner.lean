-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocal_basis_inner
-- name    : QEC.Semantics.QuditSubsystem.extendLocal_basis_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:08:36.124463+00:00
-- url     : https://prove2.me/theorems/dfd031c6-cbe6-4da7-af9a-4b308e9c5920
-- title:
--   Qudit Subsystem: extend Local basis inner
-- statement:
--   The Qudit Subsystem construction uses the extend Local basis inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditMatrixElements.lean#L20-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditMatrixElements.lean#L20-L34

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditMatrixElements
set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.QuditSubsystem
open scoped BigOperators TensorProduct
universe u
variable {J : Type u} [Fintype J] [DecidableEq J] {q : J → Nat}

theorem QEC.Semantics.QuditSubsystem.extendLocal_basis_inner (S : QuditSubsystem q) (E : Operator S.selectedSystem)
    (x y : Qudit.Label q) :
    inner Complex (EuclideanSpace.basisFun (Qudit.Label q) Complex x)
      (S.extendLocalToRegister E (EuclideanSpace.basisFun (Qudit.Label q) Complex y)) =
    inner Complex
        (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex (S.splitLabel x).1)
        (E (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex (S.splitLabel y).1)) *
      inner Complex
        (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex (S.splitLabel x).2)
        (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex (S.splitLabel y).2) := by sorry
