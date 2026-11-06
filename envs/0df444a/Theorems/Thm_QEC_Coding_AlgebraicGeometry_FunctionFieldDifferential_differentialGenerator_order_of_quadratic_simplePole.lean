-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialGenerator_order_of_quadratic_simplePole
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialGenerator_order_of_quadratic_simplePole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:43:14.626227+00:00
-- url     : https://prove2.me/theorems/2c27dc68-f6ba-4e01-9ca9-95b33a2d716a
-- title:
--   Function Field Differential: differential Generator order of quadratic simple Pole
-- statement:
--   The displayed characteristic-two simple-pole equation gives precisely
--   the source's weak-different correction for actual differential orders.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialStepOrder.lean#L51-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialStepOrder.lean#L51-L75

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

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialGenerator_order_of_quadratic_simplePole [CharP L 2]
    (P : GlobalPlace k K) (Q : GlobalPlace k L) (e : ℕ)
    (horder : ∀ x : K, x ≠ 0 → Q.order (algebraMap K L x) = (e : ℤ) * P.order x)
    (a : K) (y : L) (ha : P.order a = -1) (hyorder : Q.order y = -1)
    (hy : y ^ 2 + y = algebraMap K L a) :
    differentialOrder Q (functionFieldDifferentialGenerator (k := k) (F := L))
        functionFieldDifferentialGenerator_ne_zero =
      (e : ℤ) * differentialOrder P (functionFieldDifferentialGenerator (k := k) (F := K))
        functionFieldDifferentialGenerator_ne_zero + 2 * ((e : ℤ) - 1) := by sorry
