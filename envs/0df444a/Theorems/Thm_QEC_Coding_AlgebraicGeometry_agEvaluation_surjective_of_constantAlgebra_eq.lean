-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_surjective_of_constantAlgebra_eq
-- name    : QEC.Coding.AlgebraicGeometry.agEvaluation_surjective_of_constantAlgebra_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:18:02.754915+00:00
-- url     : https://prove2.me/theorems/75506290-9ab3-4d47-b1d2-f2d38ee9f2b6
-- title:
--   Algebraic Geometry: ag Evaluation surjective of constant Algebra eq
-- statement:
--   Interpolation is preserved under a proved equality of constant-field algebras.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/ConstantFieldTransport.lean#L80-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/ConstantFieldTransport.lean#L80-L90

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_CodeDuality
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_ResiduePairing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationInterpolation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_ConstantFieldTransport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (k F : Type*) [Field k] [Fintype k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
variable [κ : Algebra k F]
variable [@IsFullConstantField k F _ _ (@AffinePlace.constantAlgebra k F _ _ π)]
variable {ι : Type*} [Fintype ι]

theorem QEC.Coding.AlgebraicGeometry.agEvaluation_surjective_of_constantAlgebra_eq
    (hκ : κ = @AffinePlace.constantAlgebra k F _ _ π)
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0)
    (hlarge : 2 * (GlobalPlace.functionFieldGenus
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 1 ≤
        Divisor.degree GlobalPlace.residueDegree G - Fintype.card ι) :
    Function.Surjective (agEvaluationLinearMap G Q hG) := by sorry
