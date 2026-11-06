-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_affinePrincipalDivisor_apply
-- name    : QEC.Coding.AlgebraicGeometry.AffinePlace.affinePrincipalDivisor_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:11:05.325723+00:00
-- url     : https://prove2.me/theorems/eae40358-b12b-4010-b548-d7ef75a018cb
-- title:
--   Affine Place: affine Principal Divisor apply
-- statement:
--   The coefficient of the affine principal divisor is the normalized order
--   at that affine place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/AffinePrincipalDivisor.lean#L96-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/AffinePrincipalDivisor.lean#L96-L99

import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.DedekindDomain.Factorization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero nonZeroDivisors
open QEC.Coding.AlgebraicGeometry.AffinePlace
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.AffinePlace._p2m_local_instance_63657f3d4b_35

theorem QEC.Coding.AlgebraicGeometry.AffinePlace.affinePrincipalDivisor_apply (f : Fˣ) (P : carrier k F) :
    affinePrincipalDivisor k F f P = GlobalPlace.order (globalPlace k F P) (f : F) := by sorry
