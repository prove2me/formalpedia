-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_count_chartFractionalLattice
-- name    : QEC.Coding.AlgebraicGeometry.AffinePlace.count_chartFractionalLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:12:26.159801+00:00
-- url     : https://prove2.me/theorems/03c752ba-d0f6-4665-90a0-6b625bb0b200
-- title:
--   Affine Place: count chart Fractional Lattice
-- statement:
--   The count of the chart lattice is its prescribed prime exponent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/AffineCountBridge.lean#L43-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/AffineCountBridge.lean#L43-L46

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

theorem QEC.Coding.AlgebraicGeometry.AffinePlace.count_chartFractionalLattice (D : Divisor (carrier k F)) (P : carrier k F) :
    FractionalIdeal.count F P (chartFractionalLattice k F D) = -D P := by sorry
