-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_cfc_diagonal
-- name    : QEC.Semantics.FiniteMatrixEntropy.cfc_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:46:51.039687+00:00
-- url     : https://prove2.me/theorems/2a48e4fe-0d02-4d22-a0fb-7fcd1fef9db1
-- title:
--   Finite Matrix Entropy: cfc diagonal
-- statement:
--   Functional calculus of a real diagonal matrix is pointwise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L159-L214
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L159-L214

import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder Kronecker TensorProduct
noncomputable section
open QEC.Semantics.FiniteMatrixEntropy

theorem QEC.Semantics.FiniteMatrixEntropy.cfc_diagonal {n : Type v} [Fintype n] [DecidableEq n]
    (d : n -> Real) (f : Real -> Real) :
    cfc f (Matrix.diagonal fun i => (d i : Complex)) =
      Matrix.diagonal fun i => (f (d i) : Complex) := by sorry
