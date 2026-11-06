-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_realTrace_toMatrix
-- name    : QEC.Semantics.FiniteMatrixEntropy.realTrace_toMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:43:57.991936+00:00
-- url     : https://prove2.me/theorems/de19dd5c-7349-4097-ae1f-055f55390457
-- title:
--   Finite Matrix Entropy: real Trace to Matrix
-- statement:
--   Real matrix trace agrees with the trace of the represented finite operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L52-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L52-L59

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

theorem QEC.Semantics.FiniteMatrixEntropy.realTrace_toMatrix
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {n : Type v} [Fintype n] [DecidableEq n]
    (b : OrthonormalBasis n Complex H) (A : Operator H) :
    realTrace (A.toMatrix b.toBasis b.toBasis) =
      Complex.re (LinearMap.trace Complex H A) := by sorry
