-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_tendsto_weighted_log_regularization
-- name    : QEC.Semantics.FiniteMatrixEntropy.tendsto_weighted_log_regularization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:18:06.726861+00:00
-- url     : https://prove2.me/theorems/c9217dc3-68e4-4328-addb-33121caa890f
-- title:
--   Finite Matrix Entropy: tendsto weighted log regularization
-- statement:
--   Scalar support-aware convergence for the zero-eigenvalue case.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L411-L438
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L411-L438

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

theorem QEC.Semantics.FiniteMatrixEntropy.tendsto_weighted_log_regularization (d : Nat) (x : Real)
    (hx : 0 <= x) :
    Filter.Tendsto (fun n : Nat =>
      x * Real.log ((x + (1 / ((n : Real) + 1))) /
        (1 + (1 / ((n : Real) + 1)) * d))) Filter.atTop
      (nhds (x * Real.log x)) := by sorry
