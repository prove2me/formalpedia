-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_trace_mul_cfc_eq_sum_eigenvalues
-- name    : QEC.Semantics.FiniteMatrixEntropy.trace_mul_cfc_eq_sum_eigenvalues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:38:42.151636+00:00
-- url     : https://prove2.me/theorems/f1195843-2c0a-4ec6-b255-a1f42b7fd108
-- title:
--   Finite Matrix Entropy: trace mul cfc eq sum eigenvalues
-- statement:
--   A Hermitian functional-calculus trace pairing is its finite spectral sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L149-L187
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L149-L187

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder Kronecker TensorProduct
noncomputable section
open QEC.Semantics.FiniteMatrixEntropy

theorem QEC.Semantics.FiniteMatrixEntropy.trace_mul_cfc_eq_sum_eigenvalues {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian) (f : Real -> Real) :
    (A * hA.cfc f).trace =
      (∑ i, (hA.eigenvalues i * f (hA.eigenvalues i) : Real) : Complex) := by sorry
