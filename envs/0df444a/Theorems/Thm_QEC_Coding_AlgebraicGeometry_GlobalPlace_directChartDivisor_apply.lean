-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_directChartDivisor_apply
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.directChartDivisor_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:52:26.256734+00:00
-- url     : https://prove2.me/theorems/3ad47ca7-405a-4d81-aaf1-724d959c7c25
-- title:
--   Global Place: direct Chart Divisor apply
-- statement:
--   The direct-chart restriction preserves the coefficient at the associated
--   global place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/ChartContainment.lean#L47-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/ChartContainment.lean#L47-L51

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.directChartDivisor_apply
    (G : Divisor (@GlobalPlace k F _ _ _ (@AffinePlace.constantAlgebra k F _ _ π)))
    (P : AffinePlace.carrier k F) :
    GlobalPlace.directChartDivisor k F G P = G (AffinePlace.globalPlace k F P) := by sorry
