-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_eq_neg_realTrace_mul_log2Matrix_of_basis
-- name    : QEC.Semantics.DensityOperator.vonNeumannEntropy_eq_neg_realTrace_mul_log2Matrix_of_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:18:43.512097+00:00
-- url     : https://prove2.me/theorems/d0a096af-4858-4c60-b4d7-03329af4298c
-- title:
--   Density Operator: von Neumann Entropy eq neg real Trace mul log2 Matrix of basis
-- statement:
--   The entropy trace formula in arbitrary finite orthonormal coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L528-L550
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L528-L550

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
open QEC.Semantics.DensityOperator

theorem QEC.Semantics.DensityOperator.vonNeumannEntropy_eq_neg_realTrace_mul_log2Matrix_of_basis
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {n : Type v} [Fintype n] [DecidableEq n]
    (rho : DensityOperator H) (b : OrthonormalBasis n Complex H) :
    rho.vonNeumannEntropy =
      -FiniteMatrixEntropy.realTrace
        (rho.toOperator.toMatrix b.toBasis b.toBasis *
          FiniteMatrixEntropy.log2Matrix (rho.toOperator.toMatrix b.toBasis b.toBasis)
            ((LinearMap.isHermitian_toMatrix_iff b).2 rho.positive.isSymmetric)) := by sorry
