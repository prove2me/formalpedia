-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_sum_overlapWeight_row_scale
-- name    : QEC.Semantics.FiniteMatrixEntropy.sum_overlapWeight_row_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:38:54.51168+00:00
-- url     : https://prove2.me/theorems/d692ea21-b4ff-45f3-8806-8d70a5cbbf5c
-- title:
--   Finite Matrix Entropy: sum overlap Weight row scale
-- statement:
--   Row stochasticity of the eigenbasis overlap preserves a row-indexed sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L116-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L116-L125

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

theorem QEC.Semantics.FiniteMatrixEntropy.sum_overlapWeight_row_scale {n : Type u} [Fintype n] [DecidableEq n]
    (U V : Matrix.unitaryGroup n Complex) (f : n -> Real) :
    (∑ i, ∑ j, overlapWeight U V i j * f i) = ∑ i, f i := by sorry
