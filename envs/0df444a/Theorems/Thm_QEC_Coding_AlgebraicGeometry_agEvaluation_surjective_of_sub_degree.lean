-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_surjective_of_sub_degree
-- name    : QEC.Coding.AlgebraicGeometry.agEvaluation_surjective_of_sub_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:56:54.975003+00:00
-- url     : https://prove2.me/theorems/a2650403-be08-4584-9065-1527ea1a9476
-- title:
--   Algebraic Geometry: ag Evaluation surjective of sub degree
-- statement:
--   Riemann--Roch proves that arbitrary values can be prescribed on the selected places.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/EvaluationInterpolation.lean#L32-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/EvaluationInterpolation.lean#L32-L62

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationKernel
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationInterpolation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (k F : Type*) [Field k] [Fintype k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.interpolationConstantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.interpolationConstantTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.interpolationFiniteDimensional
variable [IsFullConstantField k F] {ι : Type*} [Fintype ι]

theorem QEC.Coding.AlgebraicGeometry.agEvaluation_surjective_of_sub_degree
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0)
    (hlarge : 2 * (GlobalPlace.functionFieldGenus
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 1 ≤
        Divisor.degree GlobalPlace.residueDegree G - Fintype.card ι) :
    Function.Surjective (agEvaluationLinearMap G Q hG) := by sorry
