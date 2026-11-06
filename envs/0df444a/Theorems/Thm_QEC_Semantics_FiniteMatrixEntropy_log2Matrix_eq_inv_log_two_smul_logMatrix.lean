-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_eq_inv_log_two_smul_logMatrix
-- name    : QEC.Semantics.FiniteMatrixEntropy.log2Matrix_eq_inv_log_two_smul_logMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:18:43.803338+00:00
-- url     : https://prove2.me/theorems/ccf2c9a3-7830-46ad-bb6d-53ef9393b251
-- title:
--   Finite Matrix Entropy: log2 Matrix eq inv log two smul log Matrix
-- statement:
--   Base-two matrix logarithm is the positive scalar rescaling of the natural logarithm.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L500-L512
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L500-L512

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

theorem QEC.Semantics.FiniteMatrixEntropy.log2Matrix_eq_inv_log_two_smul_logMatrix
    {n : Type v} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian) :
    log2Matrix A hA = (Real.log 2)⁻¹ • logMatrix A hA := by sorry
