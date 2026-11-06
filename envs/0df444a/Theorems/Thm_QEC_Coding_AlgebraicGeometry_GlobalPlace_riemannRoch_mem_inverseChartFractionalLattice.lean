-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRoch_mem_inverseChartFractionalLattice
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRoch_mem_inverseChartFractionalLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:05:25.722194+00:00
-- url     : https://prove2.me/theorems/fe504314-960b-428d-b369-da659efcd716
-- title:
--   Global Place: riemann Roch mem inverse Chart Fractional Lattice
-- statement:
--   A Riemann--Roch member is contained in the fractional lattice obtained by
--   restricting the same all-place divisor to the transported inverse chart.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/ChartContainment.lean#L200-L239
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/ChartContainment.lean#L200-L239

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRoch_mem_inverseChartFractionalLattice :
    letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
    ∀ (G : Divisor (GlobalPlace k F)) (x : GlobalPlace.riemannRochSubmodule G),
      letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
        (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
      letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
        (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
      (x : F) ∈ AffinePlace.chartFractionalLattice k F
        (GlobalPlace.inverseChartDivisor (π := π) (ρ := ρ) (φ := φ) (s := s) k F G) := by sorry
