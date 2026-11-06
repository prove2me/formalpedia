-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_trace_mul_cfc_diagonal
-- name    : QEC.Semantics.FiniteMatrixEntropy.trace_mul_cfc_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:42:08.763555+00:00
-- url     : https://prove2.me/theorems/18eab754-3943-446e-a7d6-f4c85f544b88
-- title:
--   Finite Matrix Entropy: trace mul cfc diagonal
-- statement:
--   A diagonal trace pairing reduces to its coordinatewise functional-calculus sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L226-L246
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L226-L246

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

theorem QEC.Semantics.FiniteMatrixEntropy.trace_mul_cfc_diagonal {n : Type u} [Fintype n] [DecidableEq n]
    (d : n -> Real) (f : Real -> Real) :
    (Matrix.diagonal (fun i => (d i : Complex)) *
        cfc f (Matrix.diagonal fun i => (d i : Complex))).trace =
      (∑ i, (d i * f (d i) : Real) : Complex) := by sorry
