-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_TwoChartFiniteDimensionalBridge_directLaurentWindowCoordinates_finiteDimensional
-- name    : QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.directLaurentWindowCoordinates_finiteDimensional
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:05:43.293231+00:00
-- url     : https://prove2.me/theorems/30e3e58e-0cd4-4ec5-86eb-8b92914249bc
-- title:
--   Two Chart Finite Dimensional Bridge: direct Laurent Window Coordinates finite Dimensional
-- statement:
--   The Two Chart Finite Dimensional Bridge construction uses the direct Laurent Window Coordinates finite Dimensional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/TwoChartFiniteDimensionalBridge.lean#L45-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/TwoChartFiniteDimensionalBridge.lean#L45-L49

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

theorem QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.directLaurentWindowCoordinates_finiteDimensional
    (k : Type*) [Field k] [Fintype ι] (lower upper : ℤ) :
    FiniteDimensional k (directLaurentWindowCoordinates k ι lower upper) := by sorry
