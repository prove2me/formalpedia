-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_TwoChartFiniteDimensionalBridge_scaled_coordinates_mem_windowCoordinates
-- name    : QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.scaled_coordinates_mem_windowCoordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:06:39.607144+00:00
-- url     : https://prove2.me/theorems/65a7cfa4-d8a4-41d6-b36f-f469766a5ca1
-- title:
--   Two Chart Finite Dimensional Bridge: scaled coordinates mem window Coordinates
-- statement:
--   Coordinatewise membership lifts to the finite direct-Laurent coordinate
--   space.  Finiteness of `ι` turns the pointwise subtype family into a Finsupp.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/TwoChartFiniteDimensionalBridge.lean#L311-L327
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/TwoChartFiniteDimensionalBridge.lean#L311-L327

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

theorem QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.scaled_coordinates_mem_windowCoordinates
    [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [Fintype ι]
    (b : Module.Basis ι (RatFunc k) F) (a d : Polynomial k) (x : F)
    (hcoordinate : ∀ j : ι,
      twoChartScaledCoordinateMap b a d x j ∈
        directLaurentWindow k (-(d.natDegree : ℤ)) (a.natDegree : ℤ)) :
    twoChartScaledCoordinateMap b a d x ∈
      directLaurentWindowCoordinates k ι (-(d.natDegree : ℤ)) (a.natDegree : ℤ) := by sorry
