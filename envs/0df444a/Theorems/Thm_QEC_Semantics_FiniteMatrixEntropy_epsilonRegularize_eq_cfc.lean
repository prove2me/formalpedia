-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_epsilonRegularize_eq_cfc
-- name    : QEC.Semantics.FiniteMatrixEntropy.epsilonRegularize_eq_cfc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:47:22.646562+00:00
-- url     : https://prove2.me/theorems/dd561603-fc7c-40e9-b09d-edb9c74b8684
-- title:
--   Finite Matrix Entropy: epsilon Regularize eq cfc
-- statement:
--   Epsilon regularization is scalar functional calculus on a Hermitian matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L337-L356
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L337-L356

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

theorem QEC.Semantics.FiniteMatrixEntropy.epsilonRegularize_eq_cfc {n : Type v} [Fintype n] [DecidableEq n]
    (B : Matrix n n Complex) (hB : B.IsHermitian) (epsilon : Real) :
    epsilonRegularize B epsilon = hB.cfc (fun x =>
      (1 + epsilon * Fintype.card n)⁻¹ * (x + epsilon)) := by sorry
