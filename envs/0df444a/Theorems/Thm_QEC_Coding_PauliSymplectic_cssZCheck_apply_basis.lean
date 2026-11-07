-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_cssZCheck_apply_basis
-- name    : QEC.Coding.PauliSymplectic.cssZCheck_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:45:33.491337+00:00
-- url     : https://prove2.me/theorems/9df2d238-115c-419b-9af6-773ca53467f4
-- title:
--   Pauli Symplectic: css ZCheck apply basis
-- statement:
--   The actual Z-check multiplies a computational word by its pairing phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/BasisAction.lean#L62-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/BasisAction.lean#L62-L86

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PauliSymplectic
open Semantics
universe u
variable {J : Type u} [Fintype J] [DecidableEq J]

theorem QEC.Coding.PauliSymplectic.cssZCheck_apply_basis (z y : Word (ZMod 2) J) :
    toQubitOperator (cssZCheck z) (EuclideanSpace.basisFun (Word (ZMod 2) J) Complex y) =
      binaryPhaseScalar (wordPairing z y) •
        EuclideanSpace.basisFun (Word (ZMod 2) J) Complex y := by sorry
