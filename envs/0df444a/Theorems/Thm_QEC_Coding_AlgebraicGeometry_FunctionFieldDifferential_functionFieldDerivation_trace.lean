-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDerivation_trace
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDerivation_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:46:25.425856+00:00
-- url     : https://prove2.me/theorems/4aa606c8-0094-42cb-928c-10f3c30f138c
-- title:
--   Function Field Differential: function Field Derivation trace
-- statement:
--   The chosen function-field derivation commutes with the field trace to the
--   rational function field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DerivationTrace.lean#L246-L280
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DerivationTrace.lean#L246-L280

import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DerivationTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped RatFunc
variable {k F : Type*} [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDerivation_trace (x : F) :
    RatFuncDerivation.rationalDerivation (k := k) (M := RatFunc k) 1
        (Algebra.trace (RatFunc k) F x) =
      Algebra.trace (RatFunc k) F
        (functionFieldDerivation (k := k) (F := F) x) := by sorry
