-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_trace_mul_logMatrix_kronecker
-- name    : QEC.Semantics.FiniteMatrixEntropy.trace_mul_logMatrix_kronecker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:42:54.998551+00:00
-- url     : https://prove2.me/theorems/e2e6e0c3-1ea4-44ff-a9fa-4040da2eb477
-- title:
--   Finite Matrix Entropy: trace mul log Matrix kronecker
-- statement:
--   The Finite Matrix Entropy construction uses the trace mul log Matrix kronecker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L485-L593
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L485-L593

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
set_option maxHeartbeats 1000000

theorem QEC.Semantics.FiniteMatrixEntropy.trace_mul_logMatrix_kronecker {m n : Type u}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m Complex) (B : Matrix n n Complex)
    (hA : A.PosDef) (hB : B.PosDef) :
    ((A ⊗ₖ B) *
        logMatrix (A ⊗ₖ B) (hA.kronecker hB).isHermitian).trace =
      (∑ i, ∑ j,
        (hA.isHermitian.eigenvalues i * hB.isHermitian.eigenvalues j *
          Real.log (hA.isHermitian.eigenvalues i * hB.isHermitian.eigenvalues j) : Real) : Complex) := by sorry
