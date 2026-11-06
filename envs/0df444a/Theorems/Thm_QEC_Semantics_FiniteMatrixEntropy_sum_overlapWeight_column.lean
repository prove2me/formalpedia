-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_sum_overlapWeight_column
-- name    : QEC.Semantics.FiniteMatrixEntropy.sum_overlapWeight_column
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:41:57.247634+00:00
-- url     : https://prove2.me/theorems/53807d07-ed33-4236-b338-089ba2403214
-- title:
--   Finite Matrix Entropy: sum overlap Weight column
-- statement:
--   Each column of a unitary overlap matrix has total squared modulus one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L103-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L103-L113

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

theorem QEC.Semantics.FiniteMatrixEntropy.sum_overlapWeight_column {n : Type u} [Fintype n] [DecidableEq n]
    (U V : Matrix.unitaryGroup n Complex) (j : n) :
    (∑ i, overlapWeight U V i j) = 1 := by sorry
