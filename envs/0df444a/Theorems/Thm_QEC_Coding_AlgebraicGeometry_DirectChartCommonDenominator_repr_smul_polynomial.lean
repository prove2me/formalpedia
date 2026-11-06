-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectChartCommonDenominator_repr_smul_polynomial
-- name    : QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator.repr_smul_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:55:15.374073+00:00
-- url     : https://prove2.me/theorems/2fea8052-9413-4ec3-a2c8-befb92f5fa7c
-- title:
--   Direct Chart Common Denominator: repr smul polynomial
-- statement:
--   Coordinate linearity for the actual tower `R → K → F`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/DirectChartCommonDenominator.lean#L48-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/DirectChartCommonDenominator.lean#L48-L52

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator
open scoped BigOperators Polynomial
variable {k F ι : Type*}
variable [Field k] [Field F]
variable [Algebra (RatFunc k) F] [Algebra (Polynomial k) F]
  [IsScalarTower (Polynomial k) (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator.repr_smul_polynomial (b : Module.Basis ι (RatFunc k) F) (a : Polynomial k) (x : F) (j : ι) :
    b.repr (a • x) j = algebraMap (Polynomial k) (RatFunc k) a * b.repr x j := by sorry
