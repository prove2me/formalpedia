-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_order_lowerBound_iff_valuation_le
-- name    : QEC.Coding.AlgebraicGeometry.AffinePlace.order_lowerBound_iff_valuation_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:12:46.04465+00:00
-- url     : https://prove2.me/theorems/37f12e56-c161-412b-aab0-6b3ad0d30f7f
-- title:
--   Affine Place: order lower Bound iff valuation le
-- statement:
--   For a nonzero element, an affine valuation bound is exactly the matching
--   lower normalized-order bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/AffineCountBridge.lean#L103-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/AffineCountBridge.lean#L103-L110

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

theorem QEC.Coding.AlgebraicGeometry.AffinePlace.order_lowerBound_iff_valuation_le (P : carrier k F) {f : F} (hf : f ≠ 0)
    (n : ℤ) :
    -n ≤ GlobalPlace.order (globalPlace k F P) f ↔
      valuation k F P f ≤ WithZero.exp n := by sorry
