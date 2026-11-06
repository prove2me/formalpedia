-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_trace_mul_logMatrix_eq_sum_eigenvalues
-- name    : QEC.Semantics.FiniteMatrixEntropy.trace_mul_logMatrix_eq_sum_eigenvalues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:38:52.370396+00:00
-- url     : https://prove2.me/theorems/11237402-2823-4a2a-b16e-ef3805790bf0
-- title:
--   Finite Matrix Entropy: trace mul log Matrix eq sum eigenvalues
-- statement:
--   The trace of `A log A` is its finite spectral sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L249-L253
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L249-L253

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

theorem QEC.Semantics.FiniteMatrixEntropy.trace_mul_logMatrix_eq_sum_eigenvalues {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian) :
    (A * logMatrix A hA).trace =
      (∑ i, (hA.eigenvalues i * Real.log (hA.eigenvalues i) : Real) : Complex) := by sorry
