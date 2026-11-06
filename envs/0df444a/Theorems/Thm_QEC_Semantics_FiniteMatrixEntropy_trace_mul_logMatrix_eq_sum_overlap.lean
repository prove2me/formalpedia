-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_trace_mul_logMatrix_eq_sum_overlap
-- name    : QEC.Semantics.FiniteMatrixEntropy.trace_mul_logMatrix_eq_sum_overlap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:42:26.167477+00:00
-- url     : https://prove2.me/theorems/936b1a26-acd2-4cce-a58f-16ff53879fe7
-- title:
--   Finite Matrix Entropy: trace mul log Matrix eq sum overlap
-- statement:
--   The Finite Matrix Entropy construction uses the trace mul log Matrix eq sum overlap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L257-L319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L257-L319

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
set_option maxHeartbeats 3000000

theorem QEC.Semantics.FiniteMatrixEntropy.trace_mul_logMatrix_eq_sum_overlap {n : Type u} [Fintype n] [DecidableEq n]
    (A B : Matrix n n Complex) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * logMatrix B hB).trace =
      (∑ i, ∑ j,
        (hA.eigenvalues i * overlapWeight hA.eigenvectorUnitary hB.eigenvectorUnitary i j *
          Real.log (hB.eigenvalues j) : Real) : Complex) := by sorry
