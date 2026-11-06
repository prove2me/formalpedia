-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_TwoChartFiniteDimensionalBridge_directLaurentToRatFunc_injective
-- name    : QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.directLaurentToRatFunc_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:06:31.61166+00:00
-- url     : https://prove2.me/theorems/cdfd6a22-42d1-4f32-a38b-d406b010b1cd
-- title:
--   Two Chart Finite Dimensional Bridge: direct Laurent To Rat Func injective
-- statement:
--   The Laurent localization maps injectively into the rational-function
--   field.  The target map is identified by localization ring-map extensionality
--   on `k[X]`; its source is `LaurentPolynomial.isLocalization`, its target is
--   the fraction-field localization, and the only submonoid inclusion sends each
--   power of `X` to a nonzero polynomial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/TwoChartFiniteDimensionalBridge.lean#L90-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/TwoChartFiniteDimensionalBridge.lean#L90-L116

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

theorem QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.directLaurentToRatFunc_injective (k : Type*) [Field k] :
    Function.Injective
      (InverseChartDenominatorTransport.directLaurentToRatFunc k) := by sorry
