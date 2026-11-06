-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_rational_differentialGenerator_order_of_order_X_zero
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.rational_differentialGenerator_order_of_order_X_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:44:08.639101+00:00
-- url     : https://prove2.me/theorems/a4c65980-3c69-45f1-b960-075101e09ef8
-- title:
--   Function Field Differential: rational differential Generator order of order X zero
-- statement:
--   At any rational-base place where the variable is a unit, dt has order
--   zero. Classification includes all finite-degree places, not just rational points.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RationalDifferentialTransport.lean#L81-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RationalDifferentialTransport.lean#L81-L92

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RationalDifferentialTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
noncomputable section
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [Algebra.IsSeparable (RatFunc k) K] [FiniteDimensional (RatFunc k) K]
variable [Finite k]

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.rational_differentialGenerator_order_of_order_X_zero
    (R : GlobalPlace k (RatFunc k)) (hX : R.order RatFunc.X = 0) :
    differentialOrder R (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
      functionFieldDifferentialGenerator_ne_zero = 0 := by sorry
