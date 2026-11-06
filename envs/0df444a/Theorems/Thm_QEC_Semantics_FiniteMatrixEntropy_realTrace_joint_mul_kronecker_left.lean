-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_realTrace_joint_mul_kronecker_left
-- name    : QEC.Semantics.FiniteMatrixEntropy.realTrace_joint_mul_kronecker_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:46:37.881191+00:00
-- url     : https://prove2.me/theorems/f37a796d-5422-474c-bde5-e5cd8eab2216
-- title:
--   Finite Matrix Entropy: real Trace joint mul kronecker left
-- statement:
--   Left marginal pairing in tensor-product matrix coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L94-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L94-L113

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

theorem QEC.Semantics.FiniteMatrixEntropy.realTrace_joint_mul_kronecker_left
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] {m n : Type u} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (bH : OrthonormalBasis m Complex H)
    (bK : OrthonormalBasis n Complex K) (A : Operator (CompositeSystem H K))
    (Y : Operator K) :
    realTrace
        (A.toMatrix (bH.tensorProduct bK).toBasis (bH.tensorProduct bK).toBasis *
          ((1 : Matrix m m Complex) ⊗ₖ Y.toMatrix bK.toBasis bK.toBasis)) =
      realTrace ((partialTraceLeftRaw H K A).toMatrix bK.toBasis bK.toBasis *
        Y.toMatrix bK.toBasis bK.toBasis) := by sorry
