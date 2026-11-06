-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectPrincipalDegree_direct_chart_degree_eq_fieldNorm_intDegree
-- name    : QEC.Coding.AlgebraicGeometry.DirectPrincipalDegree.direct_chart_degree_eq_fieldNorm_intDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:45:14.386531+00:00
-- url     : https://prove2.me/theorems/26cbc99d-949a-42fb-b697-0f4b7fabc88b
-- title:
--   Direct Principal Degree: direct chart degree eq field Norm int Degree
-- statement:
--   The direct affine principal-divisor degree is the rational degree of the
--   actual field norm.  Every finite sum in the proof arises from the selected
--   numerator or denominator normalized-factor multiset.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/DirectPrincipalDegree.lean#L379-L405
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/DirectPrincipalDegree.lean#L379-L405

import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_AffineCountBridge
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectNormCount
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectRelNormCoefficient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectPrincipalDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectPrincipalDegree
open scoped BigOperators Polynomial RatFunc WithZero nonZeroDivisors
open UniqueFactorizationMonoid
open Submodule.IsPrincipal
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectPrincipalDegree.directPrincipalDegree_constantAlgebra
attribute [local instance] directPrincipalDegree_constantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectPrincipalDegree.directPrincipalDegree_isTorsionFree
attribute [local instance] directPrincipalDegree_isTorsionFree

theorem QEC.Coding.AlgebraicGeometry.DirectPrincipalDegree.direct_chart_degree_eq_fieldNorm_intDegree (f : Fˣ) :
    Divisor.degree (AffinePlace.residueDegree k F)
      (AffinePlace.affinePrincipalDivisor k F f) =
      (Algebra.norm k⟮X⟯ (f : F)).intDegree := by sorry
