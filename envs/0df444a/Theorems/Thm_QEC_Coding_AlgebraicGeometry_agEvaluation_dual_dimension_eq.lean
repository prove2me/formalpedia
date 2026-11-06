-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_dual_dimension_eq
-- name    : QEC.Coding.AlgebraicGeometry.agEvaluation_dual_dimension_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:14:47.297385+00:00
-- url     : https://prove2.me/theorems/76d5abd2-46db-4b56-ae96-6294e965e0f2
-- title:
--   Algebraic Geometry: ag Evaluation dual dimension eq
-- statement:
--   In the source range, the genuine dual code has the complementary
--   Riemann--Roch dimension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/CodeDuality.lean#L1246-L1270
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/CodeDuality.lean#L1246-L1270

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Code
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_FunctionFieldGlobalResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarFamily
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_CodeDuality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithTop WithZero
noncomputable section
variable (k F : Type*) [Field k] [Fintype k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.agCodeDualityAlgebra
attribute [local instance] agCodeDualityAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.agCodeDualityScalarTower
attribute [local instance] agCodeDualityScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.agCodeDualityFiniteDimensional
attribute [local instance] agCodeDualityFiniteDimensional
variable [IsFullConstantField k F]
variable {ι : Type*} [Fintype ι]
variable [Nonempty ι]

theorem QEC.Coding.AlgebraicGeometry.agEvaluation_dual_dimension_eq
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0)
    (hlarge :
      2 * (GlobalPlace.functionFieldGenus
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 1 ≤
        Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G)
    (hsmall :
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G <
        Fintype.card ι) :
    (QEC.Coding.Dimension (agEvaluationCode G Q hG).dual : ℤ) =
      Fintype.card ι -
        Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G - 1 +
          (GlobalPlace.functionFieldGenus
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) := by sorry
