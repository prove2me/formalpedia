-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_sum_overlapWeight_column_scale
-- name    : QEC.Semantics.FiniteMatrixEntropy.sum_overlapWeight_column_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:42:13.190165+00:00
-- url     : https://prove2.me/theorems/a9c02460-5ff6-499b-a183-bca397ac3365
-- title:
--   Finite Matrix Entropy: sum overlap Weight column scale
-- statement:
--   Column stochasticity of the eigenbasis overlap preserves a column-indexed sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L128-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L128-L138

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

theorem QEC.Semantics.FiniteMatrixEntropy.sum_overlapWeight_column_scale {n : Type u} [Fintype n] [DecidableEq n]
    (U V : Matrix.unitaryGroup n Complex) (f : n -> Real) :
    (∑ i, ∑ j, overlapWeight U V i j * f j) = ∑ j, f j := by sorry
