-- Prove2me | Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_expansion
-- name    : QEC.Semantics.OperatorMatrix.matrixUnit_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:56:13.733146+00:00
-- url     : https://prove2.me/theorems/6c346252-68af-4786-a3de-7e355e2c2633
-- title:
--   Operator Matrix: matrix Unit expansion
-- statement:
--   Every operator expands in the matrix units associated to a finite
--   orthonormal basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Choi.lean#L87-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Choi.lean#L87-L100

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

theorem QEC.Semantics.OperatorMatrix.matrixUnit_expansion
    (b : OrthonormalBasis (Fin n) Complex H) (A : Operator H) :
    A = ∑ i : Fin n, ∑ j : Fin n,
      (b.repr (A (b j)) i) • matrixUnit b i j := by sorry
