-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRoch_eq_of_large_degree
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRoch_eq_of_large_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:53:56.028263+00:00
-- url     : https://prove2.me/theorems/bdb1c15b-e146-4177-9308-4d46839aec6b
-- title:
--   Global Place: riemann Roch eq of large degree
-- statement:
--   When `deg(G) ≥ 2g - 1`, the complementary canonical space has negative
--   degree and the Riemann--Roch dimension is exactly `deg(G) + 1 - g`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Theorem.lean#L124-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Theorem.lean#L124-L158

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRoch_eq_of_large_degree
    (G : Divisor (GlobalPlace k F))
    (hdegree :
      2 * (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
        (φ := φ) (s := s) k F : ℤ) - 1 ≤
        Divisor.degree (residueDegree (k := k) (F := F)) G) :
    (riemannRochDimension G : ℤ) =
      Divisor.degree (residueDegree (k := k) (F := F)) G + 1 -
        (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
          (φ := φ) (s := s) k F : ℤ) := by sorry
