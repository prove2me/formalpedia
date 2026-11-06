-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseFibrePrincipalDegree_inverse_fibre_degree_eq_fieldNorm_rationalInfinity_order
-- name    : QEC.Coding.AlgebraicGeometry.InverseFibrePrincipalDegree.inverse_fibre_degree_eq_fieldNorm_rationalInfinity_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:18:28.555565+00:00
-- url     : https://prove2.me/theorems/331199f6-3ba6-4ec4-8b3f-5570f1f7e082
-- title:
--   Inverse Fibre Principal Degree: inverse fibre degree eq field Norm rational Infinity order
-- statement:
--   The requested local inverse theorem.  The last equality is the established
--   coordinate-inversion and norm-functoriality bridge, with no chart parameter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/InverseFibrePrincipalDegree.lean#L631-L659
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/InverseFibrePrincipalDegree.lean#L631-L659

import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectNormCount
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectRelNormCoefficient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_RationalInfinityTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_InverseFibrePrincipalDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseFibrePrincipalDegree
open scoped BigOperators Polynomial RatFunc WithZero nonZeroDivisors
open UniqueFactorizationMonoid
open Submodule.IsPrincipal
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
local notation3 "R" => k[X]
local notation3 "B" => inverseRingOfIntegers
  (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
  (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
  (oldSeparable := oldSeparable) k F
attribute [local instance] QEC.Coding.AlgebraicGeometry.InverseFibrePrincipalDegree.inverseFibrePrincipalDegree_isTorsionFree
attribute [local instance] inverseFibrePrincipalDegree_isTorsionFree

theorem QEC.Coding.AlgebraicGeometry.InverseFibrePrincipalDegree.inverse_fibre_degree_eq_fieldNorm_rationalInfinity_order (f : Fˣ) :
    Divisor.degree (inverseFibreResidueDegree
      (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
      (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
      (oldSeparable := oldSeparable) k F)
      (inverseFibrePrincipalDivisor
        (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
        (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
        (oldSeparable := oldSeparable) k F f) =
      GlobalPlace.order (GlobalPlace.rationalInfinity k)
        (@Algebra.norm k⟮X⟯ F _ _ oldRationalAlgebra (f : F)) := by sorry
