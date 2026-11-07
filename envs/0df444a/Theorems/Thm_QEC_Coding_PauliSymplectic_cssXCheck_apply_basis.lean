-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_cssXCheck_apply_basis
-- name    : QEC.Coding.PauliSymplectic.cssXCheck_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:45:33.736342+00:00
-- url     : https://prove2.me/theorems/09a84d09-50c3-436d-838e-e9db52d928db
-- title:
--   Pauli Symplectic: css XCheck apply basis
-- statement:
--   The actual X-check sends a computational word to its translate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/BasisAction.lean#L33-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/BasisAction.lean#L33-L59

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PauliSymplectic
open Semantics
universe u
variable {J : Type u} [Fintype J] [DecidableEq J]

theorem QEC.Coding.PauliSymplectic.cssXCheck_apply_basis (x y : Word (ZMod 2) J) :
    toQubitOperator (cssXCheck x) (EuclideanSpace.basisFun (Word (ZMod 2) J) Complex y) =
      EuclideanSpace.basisFun (Word (ZMod 2) J) Complex (y + x) := by sorry
