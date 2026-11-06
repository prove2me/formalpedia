-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_TwoChartFiniteDimensionalBridge_direct_repr_inverse_polynomial_smul
-- name    : QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.direct_repr_inverse_polynomial_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:06:06.170349+00:00
-- url     : https://prove2.me/theorems/9fb6020d-8732-4349-ba59-e68809989876
-- title:
--   Two Chart Finite Dimensional Bridge: direct repr inverse polynomial smul
-- statement:
--   The coordinate of an inverse-polynomial scalar multiplication, stated in
--   the saved direct basis.  The `change` line unfolds the transported polynomial
--   map; it is the only point where the two scalar-tower records meet.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/TwoChartFiniteDimensionalBridge.lean#L134-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/TwoChartFiniteDimensionalBridge.lean#L134-L189

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

theorem QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.direct_repr_inverse_polynomial_smul
    [Field k] [Field F]
    [ρ : Algebra (RatFunc k) F] [_π : Algebra (Polynomial k) F]
    [_τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
    (b : Module.Basis ι (RatFunc k) F) (d : Polynomial k) (x : F) (j : ι) :
    let oldModule : Module (RatFunc k) F := @Algebra.toModule (RatFunc k) F _ _ ρ
    let oldBasis : @Module.Basis ι (RatFunc k) F _ _ oldModule := b
    let oldRepr := oldBasis.repr
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
    oldRepr (d • x) j =
      InverseAffinePlace.rationalInvolution k
        (algebraMap (Polynomial k) (RatFunc k) d) * oldRepr x j := by sorry
