-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_posSemidef_toMatrix_of_isPositive
-- name    : QEC.Semantics.FiniteMatrixEntropy.posSemidef_toMatrix_of_isPositive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:46:39.346814+00:00
-- url     : https://prove2.me/theorems/d871c44d-ebe4-484c-8d11-cc8ed00c289c
-- title:
--   Finite Matrix Entropy: pos Semidef to Matrix of is Positive
-- statement:
--   The joint matrix of a positive operator is positive semidefinite in any orthonormal basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L44-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L44-L49

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

theorem QEC.Semantics.FiniteMatrixEntropy.posSemidef_toMatrix_of_isPositive
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {n : Type v} [Fintype n] [DecidableEq n]
    (b : OrthonormalBasis n Complex H) (A : Operator H) (hA : A.IsPositive) :
    (A.toMatrix b.toBasis b.toBasis).PosSemidef := by sorry
