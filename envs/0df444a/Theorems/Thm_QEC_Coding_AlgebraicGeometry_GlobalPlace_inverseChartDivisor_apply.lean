-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_inverseChartDivisor_apply
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.inverseChartDivisor_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:52:19.81009+00:00
-- url     : https://prove2.me/theorems/57aa93da-eac9-4472-baa9-5bf8b0f75abc
-- title:
--   Global Place: inverse Chart Divisor apply
-- statement:
--   The inverse-chart restriction preserves the coefficient at the packaged
--   global valuation of that inverse-chart prime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/ChartContainment.lean#L168-L196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/ChartContainment.lean#L168-L196

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.inverseChartDivisor_apply
    (G : Divisor (@GlobalPlace k F _ _ _ (@AffinePlace.constantAlgebra k F _ _ π))) :
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
    ∀ P : AffinePlace.carrier k F,
      GlobalPlace.inverseChartDivisor (π := π) (ρ := ρ) (φ := φ) (s := s) k F G P =
        G (InverseAffinePlace.asGlobalPlace (π := π) (ρ := ρ) (φ := φ) (s := s) k F P) := by sorry
