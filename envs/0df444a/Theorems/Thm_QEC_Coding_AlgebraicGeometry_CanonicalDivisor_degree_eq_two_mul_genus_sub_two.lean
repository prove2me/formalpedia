-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_CanonicalDivisor_degree_eq_two_mul_genus_sub_two
-- name    : QEC.Coding.AlgebraicGeometry.CanonicalDivisor.degree_eq_two_mul_genus_sub_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:53:34.442918+00:00
-- url     : https://prove2.me/theorems/6b713f6c-ca5b-4415-a7b4-8b7dbaa6c51e
-- title:
--   Canonical Divisor: degree eq two mul genus sub two
-- statement:
--   Every actual canonical divisor has degree `2g - 2`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Theorem.lean#L94-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Theorem.lean#L94-L116

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
open QEC.Coding.AlgebraicGeometry.CanonicalDivisor

theorem QEC.Coding.AlgebraicGeometry.CanonicalDivisor.degree_eq_two_mul_genus_sub_two
    {K : Divisor (GlobalPlace k F)}
    (hK : FunctionFieldDifferential.IsCanonicalDivisor
      (k := k) (F := F) K) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) K =
      2 * (GlobalPlace.functionFieldGenus
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 2 := by sorry
