-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_realTrace_mul_log_epsilonRegularize
-- name    : QEC.Semantics.FiniteMatrixEntropy.realTrace_mul_log_epsilonRegularize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:18:00.059638+00:00
-- url     : https://prove2.me/theorems/d3bfeecc-b449-4665-b6d4-8d9846950605
-- title:
--   Finite Matrix Entropy: real Trace mul log epsilon Regularize
-- statement:
--   Spectral trace formula for the regularized logarithm.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L397-L408
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L397-L408

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

theorem QEC.Semantics.FiniteMatrixEntropy.realTrace_mul_log_epsilonRegularize
    {n : Type v} [Fintype n] [DecidableEq n]
    (B : Matrix n n Complex) (hB : B.PosSemidef) {epsilon : Real} (hepsilon : 0 < epsilon) :
    realTrace (B * logMatrix (epsilonRegularize B epsilon)
      (epsilonRegularize_posDef B hB hepsilon).isHermitian) =
      ∑ i, hB.isHermitian.eigenvalues i *
        Real.log ((hB.isHermitian.eigenvalues i + epsilon) /
          (1 + epsilon * Fintype.card n)) := by sorry
