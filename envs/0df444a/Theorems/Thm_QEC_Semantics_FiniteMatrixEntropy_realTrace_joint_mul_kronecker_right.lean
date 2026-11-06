-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_realTrace_joint_mul_kronecker_right
-- name    : QEC.Semantics.FiniteMatrixEntropy.realTrace_joint_mul_kronecker_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:46:51.729904+00:00
-- url     : https://prove2.me/theorems/e6871049-1671-4a0b-b057-c03720e6bc33
-- title:
--   Finite Matrix Entropy: real Trace joint mul kronecker right
-- statement:
--   Right marginal pairing in tensor-product matrix coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L72-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L72-L91

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

theorem QEC.Semantics.FiniteMatrixEntropy.realTrace_joint_mul_kronecker_right
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] {m n : Type u} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (bH : OrthonormalBasis m Complex H)
    (bK : OrthonormalBasis n Complex K) (A : Operator (CompositeSystem H K))
    (X : Operator H) :
    realTrace
        (A.toMatrix (bH.tensorProduct bK).toBasis (bH.tensorProduct bK).toBasis *
          (X.toMatrix bH.toBasis bH.toBasis ⊗ₖ (1 : Matrix n n Complex))) =
      realTrace (((partialTraceRightRaw H K) A).toMatrix bH.toBasis bH.toBasis *
        X.toMatrix bH.toBasis bH.toBasis) := by sorry
