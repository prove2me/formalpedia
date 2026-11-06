-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_le_of_all_count_le
-- name    : QEC.Coding.AlgebraicGeometry.AffinePlace.le_of_all_count_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:12:49.747291+00:00
-- url     : https://prove2.me/theorems/e914dc68-72b0-4f1f-bdba-222b50906e26
-- title:
--   Affine Place: le of all count le
-- statement:
--   Prime-count inequalities reverse to fractional-ideal inclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/AffineCountBridge.lean#L113-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/AffineCountBridge.lean#L113-L166

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

theorem QEC.Coding.AlgebraicGeometry.AffinePlace.le_of_all_count_le {I J : affineFractionalIdeal k F}
    (hI : I ≠ 0) (hJ : J ≠ 0)
    (hcount : ∀ P : carrier k F,
      FractionalIdeal.count F P J ≤ FractionalIdeal.count F P I) :
    I ≤ J := by sorry
