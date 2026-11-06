-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseChartDenominatorTransport_inverseBasis_coordinate_to_direct
-- name    : QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport.inverseBasis_coordinate_to_direct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:04:53.252212+00:00
-- url     : https://prove2.me/theorems/5b0a2731-3377-4e5c-8758-2dba143663ba
-- title:
--   Inverse Chart Denominator Transport: inverse Basis coordinate to direct
-- statement:
--   Inverse-basis coordinates, transported back by the actual involution, are
--   the original direct coordinates.  This unfolds `Basis.mapCoeffs` and its
--   `Finsupp.mapRange.linearEquiv` coordinate transport.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/InverseChartDenominatorTransport.lean#L125-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/InverseChartDenominatorTransport.lean#L125-L166

import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_InverseChartDenominatorTransport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport
open scoped LaurentPolynomial Polynomial RatFunc
variable {k F ι : Type*}

theorem QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport.inverseBasis_coordinate_to_direct
    [Field k] [Field F]
    [ρ : Algebra (RatFunc k) F] [π : Algebra (Polynomial k) F]
    [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
    (b : Module.Basis ι (RatFunc k) F) :
    let oldRepr := b.repr
    let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : IsScalarTower (Polynomial k) (RatFunc k) F :=
      InverseAffinePlace.transportedScalarTower (k := k) (F := F)
        (oldRationalAlgebra := ρ)
    let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    let : Algebra.IsSeparable (RatFunc k) F :=
      InverseAffinePlace.transportedIsSeparable (k := k) (F := F)
        (oldRationalAlgebra := ρ) (oldSeparable := s)
    ∀ x : F, ∀ j : ι,
      InverseAffinePlace.rationalInvolution k
        ((inverseBasis (ρ := ρ) (_π := π) (_τ := τ) (φ := φ) (s := s) b).repr x j) =
        oldRepr x j := by sorry
