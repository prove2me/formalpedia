-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_mem_chartFractionalLattice_iff
-- name    : QEC.Coding.AlgebraicGeometry.AffinePlace.mem_chartFractionalLattice_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:51:56.785728+00:00
-- url     : https://prove2.me/theorems/214a5e54-4678-48b5-8fcb-2c2ed364f4ba
-- title:
--   Affine Place: mem chart Fractional Lattice iff
-- statement:
--   Membership in the finite-chart lattice is exactly the valuation bound at
--   every actual affine height-one prime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/AffineCountBridge.lean#L170-L204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/AffineCountBridge.lean#L170-L204

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

theorem QEC.Coding.AlgebraicGeometry.AffinePlace.mem_chartFractionalLattice_iff (D : Divisor (carrier k F)) (f : F) :
    f ∈ chartFractionalLattice k F D ↔
      ∀ P : carrier k F, valuation k F P f ≤ WithZero.exp (D P) := by sorry
