-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_TwoChartFiniteDimensionalBridge_scaled_coordinate_mem_directLaurentWindow
-- name    : QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.scaled_coordinate_mem_directLaurentWindow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:06:13.648834+00:00
-- url     : https://prove2.me/theorems/c42a23f4-eaf7-4a7f-b2a5-1c5efd171c85
-- title:
--   Two Chart Finite Dimensional Bridge: scaled coordinate mem direct Laurent Window
-- statement:
--   A direct-coordinate equality and an inverse-coordinate equality place the
--   same scaled coordinate in the fixed Laurent exponent window.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/TwoChartFiniteDimensionalBridge.lean#L193-L307
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/TwoChartFiniteDimensionalBridge.lean#L193-L307

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

theorem QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.scaled_coordinate_mem_directLaurentWindow
    [Field k] [Field F] [Algebra k F]
    [ρ : Algebra (RatFunc k) F] [π : Algebra (Polynomial k) F]
    [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F]
    [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
    (b : Module.Basis ι (RatFunc k) F) (a d : Polynomial k) (x : F) (j : ι)
    (hdirect : ∃ p : Polynomial k,
      b.repr (a • x) j = algebraMap (Polynomial k) (RatFunc k) p)
    (hinverse :
      let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      let : IsScalarTower (Polynomial k) (RatFunc k) F :=
        InverseAffinePlace.transportedScalarTower
          (k := k) (F := F) (oldRationalAlgebra := ρ)
      let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
        (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
      let : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
        (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
      ∃ q : Polynomial k,
        InverseAffinePlace.rationalInvolution k
          ((InverseChartDenominatorTransport.inverseBasis
            (ρ := ρ) (_π := π) (_τ := τ) (φ := φ) (s := s) b).repr (d • x) j) =
          InverseChartDenominatorTransport.directLaurentToRatFunc k
            (InverseChartDenominatorTransport.inverseLaurentCoordinate k q)) :
    twoChartScaledCoordinateMap b a d x j ∈
      directLaurentWindow k (-(d.natDegree : ℤ)) (a.natDegree : ℤ) := by sorry
