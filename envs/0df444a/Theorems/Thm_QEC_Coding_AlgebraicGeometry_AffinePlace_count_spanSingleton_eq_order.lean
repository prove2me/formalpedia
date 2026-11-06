-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_count_spanSingleton_eq_order
-- name    : QEC.Coding.AlgebraicGeometry.AffinePlace.count_spanSingleton_eq_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:12:27.051391+00:00
-- url     : https://prove2.me/theorems/13e5f5a4-52c9-47b2-b802-0e3c7f1bab3d
-- title:
--   Affine Place: count span Singleton eq order
-- statement:
--   The exact normalized affine-order form of the principal-count bridge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/AffineCountBridge.lean#L88-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/AffineCountBridge.lean#L88-L99

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

theorem QEC.Coding.AlgebraicGeometry.AffinePlace.count_spanSingleton_eq_order (P : carrier k F) {f : F} (hf : f ≠ 0) :
    FractionalIdeal.count F P
        (FractionalIdeal.spanSingleton (affineRing k F)⁰ f) =
      GlobalPlace.order (globalPlace k F P) f := by sorry
