-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_tendsto_realTrace_mul_log_epsilonRegularize
-- name    : QEC.Semantics.FiniteMatrixEntropy.tendsto_realTrace_mul_log_epsilonRegularize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:18:25.117684+00:00
-- url     : https://prove2.me/theorems/7b9142f6-d5f1-444d-a975-4cf02bbf98cd
-- title:
--   Finite Matrix Entropy: tendsto real Trace mul log epsilon Regularize
-- statement:
--   Epsilon-to-zero bridge for a possibly singular finite PSD matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L441-L465
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L441-L465

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

theorem QEC.Semantics.FiniteMatrixEntropy.tendsto_realTrace_mul_log_epsilonRegularize
    {n : Type v} [Fintype n] [DecidableEq n]
    (B : Matrix n n Complex) (hB : B.PosSemidef) :
    Filter.Tendsto (fun k : Nat =>
      realTrace (B * logMatrix (epsilonRegularize B (1 / ((k : Real) + 1)))
        (epsilonRegularize_posDef B hB (by positivity)).isHermitian)) Filter.atTop
      (nhds (realTrace (B * logMatrix B hB.isHermitian))) := by sorry
