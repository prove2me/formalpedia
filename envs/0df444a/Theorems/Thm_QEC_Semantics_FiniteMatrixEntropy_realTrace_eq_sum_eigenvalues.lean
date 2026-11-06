-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_realTrace_eq_sum_eigenvalues
-- name    : QEC.Semantics.FiniteMatrixEntropy.realTrace_eq_sum_eigenvalues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:38:48.534612+00:00
-- url     : https://prove2.me/theorems/54f02937-69c6-4a2b-8bf2-ef0dd2e38a45
-- title:
--   Finite Matrix Entropy: real Trace eq sum eigenvalues
-- statement:
--   The real trace of a finite Hermitian matrix is the sum of its real eigenvalues.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L141-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L141-L146

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

theorem QEC.Semantics.FiniteMatrixEntropy.realTrace_eq_sum_eigenvalues {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian) :
    realTrace A = ∑ i, hA.eigenvalues i := by sorry
