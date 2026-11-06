-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_realTrace_joint_mul_kronecker_left_matrix
-- name    : QEC.Semantics.FiniteMatrixEntropy.realTrace_joint_mul_kronecker_left_matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:46:39.4012+00:00
-- url     : https://prove2.me/theorems/365fe3cf-3ef7-4443-9d76-4d5e8e7efe49
-- title:
--   Finite Matrix Entropy: real Trace joint mul kronecker left matrix
-- statement:
--   Left marginal pairing directly for a matrix observable in fixed coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L131-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L131-L143

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

theorem QEC.Semantics.FiniteMatrixEntropy.realTrace_joint_mul_kronecker_left_matrix
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] {m n : Type u} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (bH : OrthonormalBasis m Complex H)
    (bK : OrthonormalBasis n Complex K) (A : Operator (CompositeSystem H K))
    (Y : Matrix n n Complex) :
    realTrace
        (A.toMatrix (bH.tensorProduct bK).toBasis (bH.tensorProduct bK).toBasis *
          ((1 : Matrix m m Complex) ⊗ₖ Y)) =
      realTrace ((partialTraceLeftRaw H K A).toMatrix bK.toBasis bK.toBasis * Y) := by sorry
