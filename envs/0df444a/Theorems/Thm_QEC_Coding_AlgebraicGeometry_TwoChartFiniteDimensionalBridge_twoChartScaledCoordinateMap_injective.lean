-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_TwoChartFiniteDimensionalBridge_twoChartScaledCoordinateMap_injective
-- name    : QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.twoChartScaledCoordinateMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:06:27.660599+00:00
-- url     : https://prove2.me/theorems/c82930f8-68c0-4115-a1a5-f3a94fde0f4c
-- title:
--   Two Chart Finite Dimensional Bridge: two Chart Scaled Coordinate Map injective
-- statement:
--   The scaled coordinate map is injective when both actual polynomial
--   denominators are nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/TwoChartFiniteDimensionalBridge.lean#L331-L355
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/TwoChartFiniteDimensionalBridge.lean#L331-L355

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

theorem QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.twoChartScaledCoordinateMap_injective
    [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F]
    (b : Module.Basis ι (RatFunc k) F) {a d : Polynomial k} (ha : a ≠ 0) (hd : d ≠ 0) :
    Function.Injective (twoChartScaledCoordinateMap b a d) := by sorry
