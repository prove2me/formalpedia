-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_TwoChartFiniteDimensionalBridge_directLaurent_directCoordinate
-- name    : QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.directLaurent_directCoordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:06:29.501212+00:00
-- url     : https://prove2.me/theorems/2800f018-5c40-436b-b815-875b7faf6c8e
-- title:
--   Two Chart Finite Dimensional Bridge: direct Laurent direct Coordinate
-- statement:
--   Direct Laurent coordinates of direct polynomials are the ordinary
--   polynomial image in the rational-function field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/TwoChartFiniteDimensionalBridge.lean#L120-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/TwoChartFiniteDimensionalBridge.lean#L120-L129

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_InverseChartDenominatorTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
open scoped LaurentPolynomial Polynomial RatFunc
variable {k F ι : Type*}

theorem QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.directLaurent_directCoordinate
    (k : Type*) [Field k] (p : Polynomial k) :
    InverseChartDenominatorTransport.directLaurentToRatFunc k
      (LaurentFiniteWindow.directCoordinate k p) =
      algebraMap (Polynomial k) (RatFunc k) p := by sorry
