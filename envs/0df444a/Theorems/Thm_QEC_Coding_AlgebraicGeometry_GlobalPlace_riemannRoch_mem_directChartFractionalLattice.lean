-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRoch_mem_directChartFractionalLattice
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRoch_mem_directChartFractionalLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:05:30.751219+00:00
-- url     : https://prove2.me/theorems/ab54c35e-3935-408b-a7b1-9085cafe125e
-- title:
--   Global Place: riemann Roch mem direct Chart Fractional Lattice
-- statement:
--   A Riemann--Roch member is contained in the fractional lattice obtained by
--   restricting its all-place divisor to the direct affine chart.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/ChartContainment.lean#L55-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/ChartContainment.lean#L55-L71

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_AffineCountBridge
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Space
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_ChartContainment
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
variable [τ : IsScalarTower k[X] k⟮X⟯ F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable k⟮X⟯ F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRoch_mem_directChartFractionalLattice :
    letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
    ∀ (G : Divisor (GlobalPlace k F)) (x : GlobalPlace.riemannRochSubmodule G),
      (x : F) ∈ AffinePlace.chartFractionalLattice k F
        (GlobalPlace.directChartDivisor k F G) := by sorry
