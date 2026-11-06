-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocal_basis_diagonal_eq
-- name    : QEC.Semantics.QuditSubsystem.extendLocal_basis_diagonal_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:33:21.725162+00:00
-- url     : https://prove2.me/theorems/c58c09ec-1df8-42ae-93c3-5fc1e2a8f4ae
-- title:
--   Qudit Subsystem: extend Local basis diagonal eq
-- statement:
--   The Qudit Subsystem construction uses the extend Local basis diagonal eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditMatrixElements.lean#L48-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditMatrixElements.lean#L48-L59

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditMatrixElements
set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.QuditSubsystem
open scoped BigOperators TensorProduct
universe u
variable {J : Type u} [Fintype J] [DecidableEq J] {q : J → Nat}

theorem QEC.Semantics.QuditSubsystem.extendLocal_basis_diagonal_eq (S : QuditSubsystem q) (E : Operator S.selectedSystem)
    (x y : Qudit.Label q) (h : ∀ j, j ∈ S.selected → x j = y j) :
    inner Complex (EuclideanSpace.basisFun (Qudit.Label q) Complex x)
      (S.extendLocalToRegister E (EuclideanSpace.basisFun (Qudit.Label q) Complex x)) =
    inner Complex (EuclideanSpace.basisFun (Qudit.Label q) Complex y)
      (S.extendLocalToRegister E (EuclideanSpace.basisFun (Qudit.Label q) Complex y)) := by sorry
