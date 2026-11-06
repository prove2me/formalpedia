-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialTrace_differential
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDifferentialTrace_differential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:15:36.925018+00:00
-- url     : https://prove2.me/theorems/aa42af73-6fc5-4553-b482-ed2707039f24
-- title:
--   Function Field Differential: function Field Differential Trace differential
-- statement:
--   Differential trace commutes with the universal differential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialTrace.lean#L60-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialTrace.lean#L60-L70

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DerivationTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped RatFunc
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDifferentialTrace_differential (x : F) :
    functionFieldDifferentialTrace (k := k) (F := F) (differential k F x) =
      differential k (RatFunc k) (Algebra.trace (RatFunc k) F x) := by sorry
