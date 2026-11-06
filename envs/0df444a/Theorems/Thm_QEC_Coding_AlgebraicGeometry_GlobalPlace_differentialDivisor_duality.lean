-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_differentialDivisor_duality
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.differentialDivisor_duality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:49:57.157128+00:00
-- url     : https://prove2.me/theorems/1613fc5a-3872-4782-8525-3edf8570ffbb
-- title:
--   Global Place: differential Divisor duality
-- statement:
--   Multiplication by the realized nonzero differential identifies the
--   Riemann--Roch space at `(omega) - D` with the adelic differential space at
--   `D`, hence its dimension is the specialty index at `D`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleDifferentialDuality.lean#L105-L202
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleDifferentialDuality.lean#L105-L202

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialWeil
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialDuality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleDifferentialDualityAlgebra
attribute [local instance] globalAdeleDifferentialDualityAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleDifferentialDualityScalarTower
attribute [local instance] globalAdeleDifferentialDualityScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable [IsFullConstantField k F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleDifferentialDualityRiemannRochFiniteDimensional
attribute [local instance] globalAdeleDifferentialDualityRiemannRochFiniteDimensional

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.differentialDivisor_duality
    (omega : Differential k F) (homega : omega ≠ 0)
    (D : Divisor (GlobalPlace k F)) :
    riemannRochDimension
        (FunctionFieldDifferential.differentialDivisor
          (k := k) (F := F) omega homega - D) =
      riemannRochIndexOfSpecialty
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D := by sorry
