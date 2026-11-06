-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_sum_overlapWeight_row
-- name    : QEC.Semantics.FiniteMatrixEntropy.sum_overlapWeight_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:41:30.84801+00:00
-- url     : https://prove2.me/theorems/b2bd7422-19d4-4774-9521-06bbb69ecde6
-- title:
--   Finite Matrix Entropy: sum overlap Weight row
-- statement:
--   Each row of a unitary overlap matrix has total squared modulus one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L89-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L89-L100

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

theorem QEC.Semantics.FiniteMatrixEntropy.sum_overlapWeight_row {n : Type u} [Fintype n] [DecidableEq n]
    (U V : Matrix.unitaryGroup n Complex) (i : n) :
    (∑ j, overlapWeight U V i j) = 1 := by sorry
