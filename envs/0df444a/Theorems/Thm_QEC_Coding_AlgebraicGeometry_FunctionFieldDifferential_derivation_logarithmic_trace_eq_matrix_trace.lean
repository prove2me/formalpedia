-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_derivation_logarithmic_trace_eq_matrix_trace
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.derivation_logarithmic_trace_eq_matrix_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:46:29.067412+00:00
-- url     : https://prove2.me/theorems/55251468-14d5-4176-a154-06f168f8802b
-- title:
--   Function Field Differential: derivation logarithmic trace eq matrix trace
-- statement:
--   The trace of a logarithmic derivative can be computed from the
--   entrywise derivative of one multiplication matrix.  The connection terms
--   introduced by differentiating the chosen basis cancel by cyclicity of matrix
--   trace.  This weighted form is the matrix bridge used by the wild-ramification
--   local residue argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DerivationTrace.lean#L153-L236
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DerivationTrace.lean#L153-L236

import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DerivationTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped RatFunc
variable {k K L : Type*} [Field k] [Field K] [Field L]
variable [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
variable [FiniteDimensional K L]

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.derivation_logarithmic_trace_eq_matrix_trace
    (D₀ : Derivation k K K) (D : Derivation k L L)
    (hD : ∀ c : K, D (algebraMap K L c) = algebraMap K L (D₀ c))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L)
    (r t : L) (ht : t ≠ 0) :
    Algebra.trace K L (r * D t * t⁻¹) =
      Matrix.trace
        (LinearMap.toMatrix b b (Algebra.lmul K L r) *
          LinearMap.toMatrix b b (Algebra.lmul K L t⁻¹) *
            entrywiseMatrixDerivation D₀
              (LinearMap.toMatrix b b (Algebra.lmul K L t))) := by sorry
