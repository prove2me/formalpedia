-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseChartDenominatorTransport_inverseLaurentToRatFunc_eq_rationalInvolutionOnPolynomial
-- name    : QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport.inverseLaurentToRatFunc_eq_rationalInvolutionOnPolynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:56:51.565568+00:00
-- url     : https://prove2.me/theorems/1f0b6249-6ec7-4321-b994-72c47a4bf840
-- title:
--   Inverse Chart Denominator Transport: inverse Laurent To Rat Func eq rational Involution On Polynomial
-- statement:
--   The two concrete rational maps agree.  The proof is deliberately by
--   polynomial-ring extensionality: constants use the algebra-map laws, while the
--   single generator uses `rationalInvolution_X`, `invert_T`, and `eval₂_T`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/InverseChartDenominatorTransport.lean#L40-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/InverseChartDenominatorTransport.lean#L40-L50

import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_InverseChartDenominatorTransport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport
open scoped LaurentPolynomial Polynomial RatFunc
variable {k F ι : Type*}

theorem QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport.inverseLaurentToRatFunc_eq_rationalInvolutionOnPolynomial
    (k : Type*) [Field k] :
    inverseLaurentToRatFunc k = rationalInvolutionOnPolynomial k := by sorry
