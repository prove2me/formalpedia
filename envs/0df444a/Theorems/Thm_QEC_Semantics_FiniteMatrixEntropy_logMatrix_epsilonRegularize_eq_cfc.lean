-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_epsilonRegularize_eq_cfc
-- name    : QEC.Semantics.FiniteMatrixEntropy.logMatrix_epsilonRegularize_eq_cfc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:18:03.875259+00:00
-- url     : https://prove2.me/theorems/4ad59642-3ccd-4e3d-af5a-a5e285fe4faa
-- title:
--   Finite Matrix Entropy: log Matrix epsilon Regularize eq cfc
-- statement:
--   The logarithm of a regularized PSD matrix in the original spectral basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L359-L394
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L359-L394

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

theorem QEC.Semantics.FiniteMatrixEntropy.logMatrix_epsilonRegularize_eq_cfc
    {n : Type v} [Fintype n] [DecidableEq n]
    (B : Matrix n n Complex) (hB : B.PosSemidef) {epsilon : Real} (hepsilon : 0 < epsilon) :
    logMatrix (epsilonRegularize B epsilon)
        (epsilonRegularize_posDef B hB hepsilon).isHermitian =
      hB.isHermitian.cfc (fun x =>
        Real.log ((x + epsilon) / (1 + epsilon * Fintype.card n))) := by sorry
