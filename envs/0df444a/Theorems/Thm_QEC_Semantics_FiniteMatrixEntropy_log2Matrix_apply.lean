-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
-- name    : QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:38:34.808215+00:00
-- url     : https://prove2.me/theorems/746e9329-0703-46bd-b980-d922d4f365c6
-- title:
--   Finite Matrix Entropy: log2 Matrix apply
-- statement:
--   The Finite Matrix Entropy construction uses the log2 Matrix apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L55-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L55-L58

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

theorem QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian) :
    log2Matrix A hA = hA.cfc (Real.logb 2) := by sorry

attribute [defeq] QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply
