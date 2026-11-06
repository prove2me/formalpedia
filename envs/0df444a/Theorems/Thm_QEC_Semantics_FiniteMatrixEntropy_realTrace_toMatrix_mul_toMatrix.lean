-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_realTrace_toMatrix_mul_toMatrix
-- name    : QEC.Semantics.FiniteMatrixEntropy.realTrace_toMatrix_mul_toMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:44:36.848693+00:00
-- url     : https://prove2.me/theorems/32393767-6adf-4c4c-a73e-b69ecc672e01
-- title:
--   Finite Matrix Entropy: real Trace to Matrix mul to Matrix
-- statement:
--   Matrix coordinates preserve a composition trace pairing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L62-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L62-L69

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

theorem QEC.Semantics.FiniteMatrixEntropy.realTrace_toMatrix_mul_toMatrix
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {n : Type v} [Fintype n] [DecidableEq n]
    (b : OrthonormalBasis n Complex H) (A X : Operator H) :
    realTrace (A.toMatrix b.toBasis b.toBasis * X.toMatrix b.toBasis b.toBasis) =
      Complex.re (LinearMap.trace Complex H (A.comp X)) := by sorry
