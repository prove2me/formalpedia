-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_le_dual_of_residue_of_constantAlgebra_eq
-- name    : QEC.Coding.AlgebraicGeometry.agEvaluation_le_dual_of_residue_of_constantAlgebra_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:18:40.623168+00:00
-- url     : https://prove2.me/theorems/4fb60e55-3e29-402c-adad-a02b40626cdc
-- title:
--   Algebraic Geometry: ag Evaluation le dual of residue of constant Algebra eq
-- statement:
--   Orthogonality for a specified differential, under an equal constant algebra.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/ConstantFieldTransport.lean#L64-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/ConstantFieldTransport.lean#L64-L77

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
omit [@IsFullConstantField k F _ _ (@AffinePlace.constantAlgebra k F _ _ π)]

theorem QEC.Coding.AlgebraicGeometry.agEvaluation_le_dual_of_residue_of_constantAlgebra_eq
    [IsScalarTower k (RatFunc k) F]
    (hκ : κ = @AffinePlace.constantAlgebra k F _ _ π)
    (G H : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0) (hH : ∀ j, H (Q j).place = 0)
    (eta : Differential k F) (heta : eta ≠ 0)
    (etaAt : ∀ j, Differential.simplePoleDifferentialLattice (Q j).place)
    (hAt : ∀ j, (etaAt j : Differential k F) = eta)
    (hres : ∀ j, Differential.simplePoleResidue (Q j).place (etaAt j) = 1)
    (hGH : G + H ≤ FunctionFieldDifferential.differentialDivisor eta heta + evaluationDivisor Q) :
    (agEvaluationCode H Q hH).carrier ≤ (agEvaluationCode G Q hG).dual.carrier := by sorry
