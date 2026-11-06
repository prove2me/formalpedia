-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDimension_basis_polarFamily_lower_bound
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension_basis_polarFamily_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:57:12.422205+00:00
-- url     : https://prove2.me/theorems/8b252dd8-6448-41b5-9553-101ac17ce161
-- title:
--   Global Place: riemann Roch Dimension basis polar Family lower bound
-- statement:
--   The explicit family `b_i X^j`, for `0 ≤ j ≤ r`, gives the lower
--   dimension bound along the pole-divisor ray.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/PolarFamily.lean#L269-L302
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/PolarFamily.lean#L269-L302

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_EffectiveDimensionBound
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarFamily
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Polynomial Submodule
open scoped BigOperators Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochPolarFamilyAlgebra
attribute [local instance] riemannRochPolarFamilyAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochPolarFamilyPolynomialScalarTower
attribute [local instance] riemannRochPolarFamilyPolynomialScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochPolarFamilyRationalScalarTower
attribute [local instance] riemannRochPolarFamilyRationalScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochPolarFamilyFiniteDimensional
attribute [local instance] riemannRochPolarFamilyFiniteDimensional

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension_basis_polarFamily_lower_bound {n r : ℕ}
    (b : Module.Basis (Fin n) (RatFunc k) F) :
    n * (r + 1) ≤ riemannRochDimension
      (basisPoleBound (k := k) (F := F) b +
        r • polarDivisor (k := k) (F := F)
          (chartVariable (k := k) (F := F))) := by sorry
