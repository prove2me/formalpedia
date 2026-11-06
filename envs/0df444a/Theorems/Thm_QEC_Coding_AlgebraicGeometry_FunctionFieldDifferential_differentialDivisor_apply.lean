-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialDivisor_apply
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:22:48.683478+00:00
-- url     : https://prove2.me/theorems/f2523578-10d6-4ad7-8edc-09d8d2a51162
-- title:
--   Function Field Differential: differential Divisor apply
-- statement:
--   A coefficient of the divisor of a chosen differential is its intrinsic local order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/CanonicalDifferential.lean#L1023-L1026
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/CanonicalDifferential.lean#L1023-L1026

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped RatFunc
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor_apply
    (omega : Differential k F) (homega : omega ≠ 0) (P : GlobalPlace k F) :
    differentialDivisor (k := k) (F := F) omega homega P =
      differentialOrder (k := k) (F := F) P omega homega := by sorry
