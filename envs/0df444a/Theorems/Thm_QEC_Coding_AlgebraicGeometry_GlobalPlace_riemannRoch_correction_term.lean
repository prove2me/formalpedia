-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRoch_correction_term
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRoch_correction_term
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:53:37.359947+00:00
-- url     : https://prove2.me/theorems/ed5c3ca5-5e8a-47b8-8ca3-76bbb3c81922
-- title:
--   Global Place: riemann Roch correction term
-- statement:
--   The Riemann--Roch correction identity for the intrinsic divisor of an
--   actual nonzero function-field differential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Theorem.lean#L55-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Theorem.lean#L55-L78

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialDuality
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochTheoremAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochTheoremScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochTheoremFiniteDimensional
variable [IsFullConstantField k F]
open QEC.Coding.AlgebraicGeometry.GlobalPlace

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRoch_correction_term
    (omega : Differential k F) (homega : omega ≠ 0)
    (G : Divisor (GlobalPlace k F)) :
    (riemannRochDimension G : ℤ) -
        (riemannRochDimension
          (FunctionFieldDifferential.differentialDivisor
            (k := k) (F := F) omega homega - G) : ℤ) =
      Divisor.degree (residueDegree (k := k) (F := F)) G + 1 -
        (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
          (φ := φ) (s := s) k F : ℤ) := by sorry
