-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_toMatrix_tensorMap
-- name    : QEC.Semantics.FiniteMatrixEntropy.toMatrix_tensorMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:43:58.382838+00:00
-- url     : https://prove2.me/theorems/1138e867-50bd-472f-8193-70385111eed0
-- title:
--   Finite Matrix Entropy: to Matrix tensor Map
-- statement:
--   Tensor-product coordinates turn a tensor map into the matrix Kronecker product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L30-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L30-L41

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

theorem QEC.Semantics.FiniteMatrixEntropy.toMatrix_tensorMap
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
    {m : Type v} [Fintype m] [DecidableEq m] {n : Type w} [Fintype n] [DecidableEq n]
    (bH : OrthonormalBasis m Complex H) (bK : OrthonormalBasis n Complex K)
    (X : Operator H) (Y : Operator K) :
    (TensorProduct.map X Y).toMatrix (bH.tensorProduct bK).toBasis
      (bH.tensorProduct bK).toBasis =
      X.toMatrix bH.toBasis bH.toBasis ⊗ₖ Y.toMatrix bK.toBasis bK.toBasis := by sorry
