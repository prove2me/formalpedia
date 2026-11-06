-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialGenerator_order_of_unramified_order_transport
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialGenerator_order_of_unramified_order_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:42:33.213713+00:00
-- url     : https://prove2.me/theorems/05346197-c0b4-4942-a503-26d5640ab37a
-- title:
--   Function Field Differential: differential Generator order of unramified order transport
-- statement:
--   Index-one order transport preserves the order of the actual common
--   rational differential generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialStepOrder.lean#L26-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialStepOrder.lean#L26-L47

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialStepOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
noncomputable section
variable {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [Algebra (RatFunc k) L]
    [IsScalarTower k (RatFunc k) K] [IsScalarTower k (RatFunc k) L]
    [IsScalarTower (RatFunc k) K L]
    [Algebra.IsSeparable (RatFunc k) K] [Algebra.IsSeparable (RatFunc k) L]
    [FiniteDimensional (RatFunc k) K] [FiniteDimensional (RatFunc k) L]

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialGenerator_order_of_unramified_order_transport
    (P : GlobalPlace k K) (Q : GlobalPlace k L)
    (horder : ∀ x : K, x ≠ 0 → Q.order (algebraMap K L x) = P.order x) :
    differentialOrder Q (functionFieldDifferentialGenerator (k := k) (F := L))
        functionFieldDifferentialGenerator_ne_zero =
      differentialOrder P (functionFieldDifferentialGenerator (k := k) (F := K))
        functionFieldDifferentialGenerator_ne_zero := by sorry
