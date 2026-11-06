-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_trace_cfc_diagonal
-- name    : QEC.Semantics.FiniteMatrixEntropy.trace_cfc_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:49:16.567204+00:00
-- url     : https://prove2.me/theorems/e98d9d2e-ca80-484e-b839-f92d4c4c94a6
-- title:
--   Finite Matrix Entropy: trace cfc diagonal
-- statement:
--   Functional-calculus trace of a real diagonal matrix, stated without choosing an eigenbasis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L204-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L204-L223

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

theorem QEC.Semantics.FiniteMatrixEntropy.trace_cfc_diagonal {n : Type u} [Fintype n] [DecidableEq n]
    (d : n -> Real) (f : Real -> Real) :
    (cfc f (Matrix.diagonal fun i => (d i : Complex))).trace =
      (∑ i, (f (d i) : Real) : Complex) := by sorry
