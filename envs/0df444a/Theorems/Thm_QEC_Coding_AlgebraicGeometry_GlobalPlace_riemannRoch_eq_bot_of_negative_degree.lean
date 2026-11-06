-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRoch_eq_bot_of_negative_degree
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRoch_eq_bot_of_negative_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:54:29.121705+00:00
-- url     : https://prove2.me/theorems/ff7c1eef-6634-4e2d-a1ad-ae2cc3c2a67e
-- title:
--   Global Place: riemann Roch eq bot of negative degree
-- statement:
--   A divisor of negative degree has the zero all-place Riemann--Roch
--   submodule.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Theorem.lean#L162-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Theorem.lean#L162-L166

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRoch_eq_bot_of_negative_degree
    (G : Divisor (GlobalPlace k F))
    (hdegree : Divisor.degree (residueDegree (k := k) (F := F)) G < 0) :
    riemannRochSubmodule G = ⊥ := by sorry
