-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_count_spanSingleton_eq_affinePrincipalCoefficient
-- name    : QEC.Coding.AlgebraicGeometry.AffinePlace.count_spanSingleton_eq_affinePrincipalCoefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:12:28.843407+00:00
-- url     : https://prove2.me/theorems/948cf71b-89d8-4c46-81c8-50f1aacd6217
-- title:
--   Affine Place: count span Singleton eq affine Principal Coefficient
-- statement:
--   The exact nonzero principal bridge.  The numerator and denominator chosen
--   by `IsLocalization.sec` are used both by `FractionalIdeal.count` and the
--   normalized affine principal coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/AffineCountBridge.lean#L61-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/AffineCountBridge.lean#L61-L85

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_AffineCountBridge
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
attribute [local instance] QEC.Coding.AlgebraicGeometry.AffinePlace._p2m_local_instance_45ffe40864_30

theorem QEC.Coding.AlgebraicGeometry.AffinePlace.count_spanSingleton_eq_affinePrincipalCoefficient (P : carrier k F)
    {f : F} (hf : f ≠ 0) :
    FractionalIdeal.count F P
        (FractionalIdeal.spanSingleton (affineRing k F)⁰ f) =
      affinePrincipalCoefficient k F P (Units.mk0 f hf) := by sorry
