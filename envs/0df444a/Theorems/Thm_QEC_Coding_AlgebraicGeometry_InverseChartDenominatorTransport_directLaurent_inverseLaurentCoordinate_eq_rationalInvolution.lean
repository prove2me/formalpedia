-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseChartDenominatorTransport_directLaurent_inverseLaurentCoordinate_eq_rationalInvolution
-- name    : QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport.directLaurent_inverseLaurentCoordinate_eq_rationalInvolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:56:49.798896+00:00
-- url     : https://prove2.me/theorems/bb3c81f8-f2bb-4746-ba54-9e5c98550430
-- title:
--   Inverse Chart Denominator Transport: direct Laurent inverse Laurent Coordinate eq rational Involution
-- statement:
--   Pointwise form of the constructed Laurent/rational bridge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/InverseChartDenominatorTransport.lean#L53-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/InverseChartDenominatorTransport.lean#L53-L58

import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_InverseChartDenominatorTransport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport
open scoped LaurentPolynomial Polynomial RatFunc
variable {k F ι : Type*}

theorem QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport.directLaurent_inverseLaurentCoordinate_eq_rationalInvolution
    (k : Type*) [Field k] (p : k[X]) :
    directLaurentToRatFunc k (inverseLaurentCoordinate k p) =
      InverseAffinePlace.rationalInvolution k (algebraMap k[X] (RatFunc k) p) := by sorry
