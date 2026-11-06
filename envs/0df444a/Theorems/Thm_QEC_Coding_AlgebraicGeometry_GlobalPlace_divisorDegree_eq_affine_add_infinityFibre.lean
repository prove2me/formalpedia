-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_divisorDegree_eq_affine_add_infinityFibre
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.divisorDegree_eq_affine_add_infinityFibre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:02:12.551208+00:00
-- url     : https://prove2.me/theorems/922418c1-9f8b-4d70-b2ca-dcf7494694be
-- title:
--   Global Place: divisor Degree eq affine add infinity Fibre
-- statement:
--   The weighted degree of an actual all-place divisor is the sum of the
--   degrees of its genuine direct-chart and finite inverse-fibre restrictions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/PolarDegree.lean#L98-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/PolarDegree.lean#L98-L116

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_InverseFibrePrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarFamily
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochPolarDegreeAlgebra
attribute [local instance] riemannRochPolarDegreeAlgebra
open QEC.Coding.AlgebraicGeometry.GlobalPlace

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.divisorDegree_eq_affine_add_infinityFibre
    (D : Divisor (GlobalPlace k F)) :
    Divisor.degree (residueDegree (k := k) (F := F)) D =
      Divisor.degree (AffinePlace.residueDegree k F)
          (affineFinsupp (k := k) (F := F) D) +
        Divisor.degree
          (InverseAffinePlace.infinityFibreResidueDegree (k := k) (F := F))
          (infinityFibreFinsupp (k := k) (F := F) D) := by sorry
