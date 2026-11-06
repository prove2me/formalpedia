-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_dual_carrier_eq
-- name    : QEC.Coding.AlgebraicGeometry.agEvaluation_dual_carrier_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:15:47.472451+00:00
-- url     : https://prove2.me/theorems/f1fd53b4-0c02-4768-b702-c8fccdbf14a3
-- title:
--   Algebraic Geometry: ag Evaluation dual carrier eq
-- statement:
--   The genuine Euclidean dual of `C_L(D,G)` is literally the evaluation code
--   for `R + D - G`, with `R` the constructed normalized canonical divisor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/CodeDuality.lean#L1598-L1698
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/CodeDuality.lean#L1598-L1698

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

theorem QEC.Coding.AlgebraicGeometry.agEvaluation_dual_carrier_eq
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0) :
    (agEvaluationCode G Q hG).dual.carrier =
      (agEvaluationCode
        (normalizedEvaluationDualDivisor
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G)
        Q (normalizedEvaluationDualDivisor_apply_at
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
          k F Q hQ G hG)).carrier := by sorry
