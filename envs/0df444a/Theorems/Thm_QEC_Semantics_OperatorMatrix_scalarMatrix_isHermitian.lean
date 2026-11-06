-- Prove2me | Theorems.Thm_QEC_Semantics_OperatorMatrix_scalarMatrix_isHermitian
-- name    : QEC.Semantics.OperatorMatrix.scalarMatrix_isHermitian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:43.481922+00:00
-- url     : https://prove2.me/theorems/bfab1557-042a-4159-b39f-a358ad3b266a
-- title:
--   Operator Matrix: scalar Matrix is Hermitian
-- statement:
--   The scalar matrix associated to a positive block operator matrix is Hermitian.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L137-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L137-L144

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.OperatorMatrix
variable {n : Nat} {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem QEC.Semantics.OperatorMatrix.scalarMatrix_isHermitian {β : Type*} [Fintype β]
    (M : OperatorMatrix n H) (hM : IsPositive M)
    (b : OrthonormalBasis β Complex H) :
    (scalarMatrix M b).IsHermitian := by sorry
