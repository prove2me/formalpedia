-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_TwoChartFiniteDimensionalBridge_twoChartScaledCoordinateMap_apply
-- name    : QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.twoChartScaledCoordinateMap_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:06:00.462292+00:00
-- url     : https://prove2.me/theorems/f285dac8-c76a-4f78-b9a1-b302891116cd
-- title:
--   Two Chart Finite Dimensional Bridge: two Chart Scaled Coordinate Map apply
-- statement:
--   The Two Chart Finite Dimensional Bridge construction uses the two Chart Scaled Coordinate Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/TwoChartFiniteDimensionalBridge.lean#L75-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/TwoChartFiniteDimensionalBridge.lean#L75-L83

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

theorem QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.twoChartScaledCoordinateMap_apply
    [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F]
    (b : Module.Basis ι (RatFunc k) F) (a d : Polynomial k) (x : F) (j : ι) :
    twoChartScaledCoordinateMap b a d x j =
      (algebraMap (Polynomial k) (RatFunc k) a *
        InverseAffinePlace.rationalInvolution k
          (algebraMap (Polynomial k) (RatFunc k) d)) *
        b.repr x j := by sorry
