-- Prove2me | Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_adjoint
-- name    : QEC.Semantics.OperatorMatrix.matrixUnit_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:53:44.6012+00:00
-- url     : https://prove2.me/theorems/b0e0e86f-8902-4461-9ce7-4b7d082f7435
-- title:
--   Operator Matrix: matrix Unit adjoint
-- statement:
--   Matrix units are adjoint-transposes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Choi.lean#L34-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Choi.lean#L34-L41

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Choi
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
open QEC.Semantics.OperatorMatrix
variable {n : Nat} {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

theorem QEC.Semantics.OperatorMatrix.matrixUnit_adjoint (b : OrthonormalBasis (Fin n) Complex H) (i j : Fin n) :
    LinearMap.adjoint (matrixUnit b i j) = matrixUnit b j i := by sorry
