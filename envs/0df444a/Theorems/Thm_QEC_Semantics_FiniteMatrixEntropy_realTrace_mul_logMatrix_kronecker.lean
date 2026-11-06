-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_realTrace_mul_logMatrix_kronecker
-- name    : QEC.Semantics.FiniteMatrixEntropy.realTrace_mul_logMatrix_kronecker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:49:32.1216+00:00
-- url     : https://prove2.me/theorems/2e043411-7be3-4f64-be66-51ca36bf29c8
-- title:
--   Finite Matrix Entropy: real Trace mul log Matrix kronecker
-- statement:
--   Trace-level tensor logarithm rule for strictly positive finite matrices.  This
--   is the exact finite identity used when the product marginal is regularized.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L599-L662
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L599-L662

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

theorem QEC.Semantics.FiniteMatrixEntropy.realTrace_mul_logMatrix_kronecker {m n : Type u}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m Complex) (B : Matrix n n Complex)
    (hA : A.PosDef) (hB : B.PosDef) :
    realTrace ((A ⊗ₖ B) *
        logMatrix (A ⊗ₖ B) (hA.kronecker hB).isHermitian) =
      realTrace (A * logMatrix A hA.isHermitian) * realTrace B +
        realTrace A * realTrace (B * logMatrix B hB.isHermitian) := by sorry
