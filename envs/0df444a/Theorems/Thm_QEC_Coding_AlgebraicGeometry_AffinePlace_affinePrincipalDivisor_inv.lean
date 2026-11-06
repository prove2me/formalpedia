-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_affinePrincipalDivisor_inv
-- name    : QEC.Coding.AlgebraicGeometry.AffinePlace.affinePrincipalDivisor_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:12:25.271549+00:00
-- url     : https://prove2.me/theorems/77489af3-eef6-4271-a1a9-e362bd5a1769
-- title:
--   Affine Place: affine Principal Divisor inv
-- statement:
--   Inversion negates the affine principal divisor.  No assertion is made
--   about the omitted places over infinity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/AffinePrincipalDivisor.lean#L116-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/AffinePrincipalDivisor.lean#L116-L122

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

theorem QEC.Coding.AlgebraicGeometry.AffinePlace.affinePrincipalDivisor_inv (f : Fˣ) :
    affinePrincipalDivisor k F f⁻¹ = -affinePrincipalDivisor k F f := by sorry
