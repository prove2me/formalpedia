-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_chartFractionalLattice_ne_zero
-- name    : QEC.Coding.AlgebraicGeometry.AffinePlace.chartFractionalLattice_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:12:27.726297+00:00
-- url     : https://prove2.me/theorems/be3f5c3b-4e44-451b-9213-2cff483b03c2
-- title:
--   Affine Place: chart Fractional Lattice ne zero
-- statement:
--   The finite chart lattice is nonzero: it is a finite product of nonzero
--   height-one-prime powers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/AffineCountBridge.lean#L50-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/AffineCountBridge.lean#L50-L56

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

theorem QEC.Coding.AlgebraicGeometry.AffinePlace.chartFractionalLattice_ne_zero (D : Divisor (carrier k F)) :
    chartFractionalLattice k F D ≠ 0 := by sorry
