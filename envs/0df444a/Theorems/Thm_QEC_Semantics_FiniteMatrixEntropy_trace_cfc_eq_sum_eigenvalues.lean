-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_trace_cfc_eq_sum_eigenvalues
-- name    : QEC.Semantics.FiniteMatrixEntropy.trace_cfc_eq_sum_eigenvalues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:42:09.524361+00:00
-- url     : https://prove2.me/theorems/49ee7648-2cd4-4cfc-b3c8-5a9e7bf0c5e2
-- title:
--   Finite Matrix Entropy: trace cfc eq sum eigenvalues
-- statement:
--   The trace of a Hermitian functional calculus is the spectral sum of the function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L190-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L190-L201

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

theorem QEC.Semantics.FiniteMatrixEntropy.trace_cfc_eq_sum_eigenvalues {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian) (f : Real -> Real) :
    (hA.cfc f).trace = (∑ i, (f (hA.eigenvalues i) : Real) : Complex) := by sorry
